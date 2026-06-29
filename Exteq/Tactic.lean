import Mathlib
import Lean

open Lean Elab Tactic Meta

-- Try to use omega to prove equality
def tryOmega (l r : Expr) (useOmega : Bool) : MetaM (Option Expr) := do
  -- restrict to nats and ints
  if not useOmega then return none
  let ty ← inferType l
  let okType ← (do return (← isDefEq ty (mkConst ``Nat)) || (← isDefEq ty (mkConst ``Int)))
              <|> pure false
  unless okType do return none
  let goalType ← mkEq l r
  let mvar ← mkFreshExprMVar goalType
  try
    let (_, _) ← (Tactic.run mvar.mvarId! do
        Tactic.evalTactic (← `(tactic| omega))).run
    let pf ← instantiateMVars mvar
    -- no holes allowed
    if pf.hasExprMVar then return none
    return some pf
  catch _ =>
    return none

-- This handles Eq.rec / Eq.ndrec
def mkEqRecPeel (recType : Name) (α a motive refl b h : Expr) : MetaM Expr := do
  let peelMotive ← withLocalDeclD `x α fun x => do
    let aEqx ← mkEq a x
    withLocalDeclD `hx aEqx fun hx => do
      let recAtx ← mkAppOptM recType
        #[some α, some a, some motive, some refl, some x, some hx]
      let body ← mkAppM ``HEq #[recAtx, refl]
      mkLambdaFVars #[x, hx] body
  let peelRefl ← mkHEqRefl refl
  mkAppOptM ``Eq.rec #[some α, some a, some peelMotive, some peelRefl, some b, some h]

-- This handles 4-argument cast functions
def mkCastPeel (head : Name) (pre post proof val : Expr) : MetaM Expr := do
  let type ← inferType pre
  let motive ← withLocalDeclD `x type fun x => do
    let xEq ← mkEq pre x
    withLocalDeclD `h xEq fun h => do
      let cast ← mkAppOptM head #[some pre, some x, some h, some val]
      mkLambdaFVars #[x, h] (← mkAppM ``HEq #[cast, val])
  let refl ← mkHEqRefl val
  mkAppOptM ``Eq.rec #[some type, some pre, some motive, some refl, some post, some proof]

-- Peels one layer of a cast in Eq.rec form or a 4-argument cast application
def peelCast? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``Eq.rec, #[α, a, motive, refl, b, h]) =>
    try
      let hPeel ← mkEqRecPeel ``Eq.rec α a motive refl b h
      return some (refl, hPeel)
    catch _ => return none
  | (``Eq.ndrec, #[α, a, motive, m, b, h]) =>
    try
      let hPeel ← mkEqRecPeel ``Eq.ndrec α a motive m b h
      return some (m, hPeel)
    catch _ => return none
  | (head, #[pre, post, proof, val]) =>
    let isEqProof ← (do return (← inferType proof).isAppOf ``Eq) <|> pure false
    if !isEqProof then return none
    try
      let hPeel ← mkCastPeel head pre post proof val
      return some (val, hPeel)
    catch _ => return none
  | _ => return none

-- Turns `.proj typeName idx struct` into the projection function application
def unfoldProj? (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .proj typeName idx struct =>
    let env ← getEnv
    let some info := getStructureInfo? env typeName | return none
    let projApp ← mkProjection struct (info.fieldNames[idx]!)
    return some projApp
  | _ => return none

-- Collects `a = b` proofs in order to help with congruence
partial def collectIndexEqs (e : Expr) : Array Expr := Id.run do
  let mut acc := #[]
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``Eq.rec, #[_, _, _, refl, _, h]) =>
    acc := acc.push h
    acc := acc ++ collectIndexEqs refl
  | (``Eq.ndrec, #[_, _, _, refl, _, h]) =>
    acc := acc.push h
    acc := acc ++ collectIndexEqs refl
  | (_, #[_, _, proof, val]) =>
    acc := acc.push proof
    acc := acc ++ collectIndexEqs val
  | _ =>
    for a in e.getAppArgs do
      acc := acc ++ collectIndexEqs a
  return acc

-- Tries to use all idxEqs to prove `l = r`
def findIndexEq? (l r : Expr) (idxEqs : Array Expr) : MetaM (Option Expr) := do
  for Eq in idxEqs do
    match (← inferType Eq).eq? with
    | some (_, el, er) =>
      trace[debug] "eq: {Eq}, el: {el}, er: {er}"
      if (← isDefEq el l) && (← isDefEq er r) then
        return some Eq
      else if (← isDefEq el r) && (← isDefEq er l) then
        return some (← mkEqSymm Eq)
    | none => pure ()
  return none

-- Tries to use all idxEqs to prove `l ≍ r`
def findIndexHEq? (l r : Expr) (idxEqs : Array Expr) : MetaM (Option Expr) := do
  for hEq in idxEqs do
    match (← inferType hEq).heq? with
    | some (_, el, _, er) =>
      if (← isDefEq el l) && (← isDefEq er r) then
        return some hEq
      else if (← isDefEq el r) && (← isDefEq er l) then
        return some (← mkHEqSymm hEq)
    | none => pure ()
  return none

mutual

-- `f a b c ... ≍ f x y z ...` by congruency at each argument
partial def relateAppEqFn (fn : Expr) (aL aR : Array Expr) (idxEqs idxHEqs : Array Expr) (depth : Option Nat) (useOmega : Bool) : MetaM (Expr × Array MVarId) := do
  let c ← mkHCongrWithArity' fn aL.size
  let mut applied := c.proof
  let mut allHoles := []
  for i in [0:c.argKinds.size] do
    let l := aL[i]!
    let r := aR[i]!
    trace[debug] "fn: {fn}, l: {l}, r: {r}, kind is eq: {c.argKinds[i]! == .eq}, kind is heq: {c.argKinds[i]! == .heq}"
    match c.argKinds[i]! with
    | .eq =>
      let depth := if let some n := depth then some (n - 1) else none
      let (proof, holes) ← relateHEq l r idxEqs idxHEqs depth useOmega
      -- **TODO** Figure out what to do with this defeq
      let tyL ← inferType l
      let tyR ← inferType r
      unless ← isDefEq tyL tyR do throwError "eq_mod_cast: .eq on not equal sides"
      let proof ← mkAppM ``eq_of_heq #[proof]
      let (proof, holes) ← if holes.size > 0 then
        trace[debug] "trying omega: {l}, {r}"
        match ← tryOmega l r useOmega with
        | some p => pure (p, #[])
        | none => pure (proof, holes)
        else pure (proof, holes)
      applied := mkAppN applied #[l, r, proof]
      allHoles := allHoles ++ holes.toList
    | .heq =>
      let depth := if let some n := depth then some (n - 1) else none
      let (proof, holes) ← relateHEq l r idxEqs idxHEqs depth useOmega
      let (proof, holes) ← if holes.size > 0 then
        trace[debug] "trying omega: {l}, {r}"
        match ← tryOmega l r useOmega with
        | some p => pure (← mkAppM ``heq_of_eq #[p], #[])
        | none => pure (proof, holes)
        else pure (proof, holes)
      applied := mkAppN applied #[l, r, proof]
      allHoles := allHoles ++ holes.toList
    | .subsingletonInst =>
      applied := mkAppN applied #[l, r]
    | _ =>
      unless ← isDefEq l r do
        let mvar ← mkFreshExprMVar (← mkAppM ``Eq #[l, r])
        allHoles := mvar.mvarId! :: allHoles
        applied := mkAppN applied #[l, r, mvar]
        -- throwError "eq_mod_cast: arguments not equal at {i}: {l} vs {r}"
      applied := mkApp applied l
  return (applied, allHoles.toArray)

-- Recursively peel off casts and build `HEq lhs rhs`
partial def relateHEq (lhs rhs : Expr) (idxEqs idxHEqs : Array Expr) (depth : Option Nat) (useOmega : Bool) : MetaM (Expr × Array MVarId) := do
  let lhs := lhs.consumeMData
  let rhs := rhs.consumeMData
  trace[debug] "comparing: {lhs}, {rhs}"
  -- trivial equality case
  if ← isDefEq lhs rhs then
    return (← mkHEqRefl lhs, #[])
  -- lemma equality case
  if let some proof ← findIndexEq? lhs rhs idxEqs then
    return (← mkHEqOfEq proof, #[])
  -- lemma heq case
  if let some proof ← findIndexHEq? lhs rhs idxHEqs then
    return (proof, #[])
  -- peel off casts and recurse
  if let some (lInner, hL) ← peelCast? lhs then
    let (hRest, holes) ← relateHEq lInner rhs idxEqs idxHEqs depth useOmega
    return (← mkHEqTrans hL hRest, holes)
  if let some (rInner, hR) ← peelCast? rhs then
    let (hRest, holes) ← relateHEq lhs rInner idxEqs idxHEqs depth useOmega
    return (← mkHEqTrans hRest (← mkHEqSymm hR), holes)
  if let some p := ← tryOmega lhs rhs useOmega then
    return (← mkAppM ``heq_of_eq #[p], #[])
  -- try rewrite .proj to function
  if let some lhs' ← unfoldProj? lhs then
    return ← relateHEq lhs' rhs idxEqs idxHEqs depth useOmega
  if let some rhs' ← unfoldProj? rhs then
    return ← relateHEq lhs rhs' idxEqs idxHEqs depth useOmega
  -- try function application congruence
  let fL := lhs.getAppFn
  let fR := rhs.getAppFn
  let aL := lhs.getAppArgs
  let aR := rhs.getAppArgs
  trace[debug] "fL: {fL}, fR: {fR}, aL: {aL}, aR: {aR}"
  -- if aL.isEmpty || aR.isEmpty then
  --   throwError "eq_mod_cast: cannot relate {lhs} and {rhs}"
  let depth := if let some n := depth then some (n - 1) else none
  if some 0 == depth then
    let mvar ← mkFreshExprMVar (← mkAppM ``HEq #[lhs, rhs])
    return (mvar, #[mvar.mvarId!])
  if (← isDefEq fL fR) && aL.size == aR.size then
    return ← relateAppEqFn fL aL aR idxEqs idxHEqs depth useOmega
  else if aL.size > 0 && aR.size > 0 then
    let fnL := lhs.appFn!
    let fnR := rhs.appFn!
    let lastL := lhs.appArg!
    let lastR := rhs.appArg!
    let (hFn, holesFn) ← relateHEq fnL fnR idxEqs idxHEqs depth useOmega
    let (hArg, holesArg) ← relateHEq lastL lastR idxEqs idxHEqs depth useOmega
    -- if holesArg.size == 0 || holesFn.size == 0 then
    let eqProof ← mkAppM ``congr_heq #[hFn, hArg]
    return (← mkAppM ``heq_of_eq #[eqProof], holesFn ++ holesArg)
  -- else if aL.size == 0 then
  --   return ← relateHEq fL rhs idxEqs idxHEqs depth useOmega
  let mvar ← mkFreshExprMVar (← mkAppM ``HEq #[lhs, rhs])
  return (mvar, #[mvar.mvarId!])

end

def collectLocalEqs : MetaM (Array Expr) := do
  let mut eqs := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    -- keep Eq and HEq
    if ty.isAppOf ``Eq || ty.isAppOf ``HEq then
      eqs := eqs.push ldecl.toExpr
  return eqs

def splitEqs (all : Array Expr) : MetaM (Array Expr × Array Expr) := do
  let mut eqs := #[]
  let mut heqs := #[]
  for e in all do
    match (← inferType e).eq? with
    | some _ => eqs := eqs.push e
    | none => pure ()
    match (← inferType e).heq? with
    | some _ => heqs := heqs.push e
    | none => pure ()
  return (eqs, heqs)

syntax eqStar := "*"
syntax (name := eq_mod_cast) "eq_mod_cast"
  (ppSpace "+omega")? (ppSpace num)? (ppSpace "[" (eqStar <|> term),* "]")? : tactic

/--
Recurses through the structure of both sides,
proving heterogenous equality transitively through casts / rewrites.
Handles functions through heterogenous equality of the function and arguments.
Requires functions to have codomains of the same type.
Allows lemmas to be provided for equality in brackets, and a maximum recursion depth.
-/
@[tactic eq_mod_cast]
def evalEqModCast : Tactic
| `(tactic| eq_mod_cast $[+omega%$omega]? $[$n:num]? $[[ $hs,* ]]?) => withMainContext do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let depth : Option Nat := n.map (·.getNat)
  let depth := if let some n := depth then some (n + 1) else none
  let (lhs, rhs, isHEq) ← match goalType.eq? with
    | some (_, l, r) => pure (l, r, false)
    | none =>
      match goalType.getAppFnArgs with
      | (``HEq, #[_, l, _, r]) => pure (l, r, true)
      | _ => throwError "eq_mod_cast: goal not in form `a = b` or `HEq a b`."
  if ← isDefEq lhs rhs then
    throwError "eq_mod_cast: goal closes by rfl; nothing to do"
  let useOmega := omega.isSome
  let localEqs ← collectLocalEqs
  let extraEqs ← match hs with
    | none => pure (#[] : Array Expr)
    | some arr => arr.getElems.mapM fun stx => do
      instantiateMVars (← elabTerm stx none)
  trace[debug] "lhs: {lhs}, rhs: {rhs}"
  trace[debug] "extraEqs: {extraEqs}"
  let idxEqs := collectIndexEqs lhs ++ collectIndexEqs rhs ++ extraEqs ++ localEqs
  let (idxEqs, idxHEqs) ← splitEqs idxEqs
  let (hFull, holes) ← relateHEq lhs rhs idxEqs idxHEqs depth useOmega

  if isHEq then
    goal.assign (← instantiateMVars hFull)
  else
    let eqHEq ← mkAppM ``eq_of_heq #[hFull]
    goal.assign (← instantiateMVars eqHEq)
  replaceMainGoal holes.toList
| _ => throwUnsupportedSyntax
