namespace checker

// NOTE: there's no UTF8 character for α hat (nor β hat), so we use â and ĉ for existential vars

module Bidir =
  let trace = true

  /// types (A,B,C): 1 | α | â | ∀α.A | A→B
  type Type =
    | TUnset
    | TUnit
    | TBool
    | TUVar of string
    | TEVar of string
    | TAll of string * Type
    | TArrow of Type * Type
    override this.ToString () =
      match this with
      | TUnset -> "<unset>"
      | TUnit -> "()"
      | TBool -> "bool"
      | TUVar v -> "'"+v
      | TEVar v -> "^"+v
      | TAll(v, tpe) -> sprintf "∀%s. %O" v tpe
      | TArrow(arg, res) -> sprintf "%O → %O" arg res

  /// terms (x): () | x | λx.e | e e | e:A
  type Term =
    | XUnit
    | XBool of bool
    | XVar of string * Type
    | XLambda of string * Type * Term
    | XApply of Term * Term * Type
    | XAnnot of Term * Type
    | XLet of string * Term * Term
    | XIf of Term * Term * Term
    override this.ToString () =
      match this with
      | XUnit -> "()"
      | XBool v -> sprintf "%b" v
      | XVar(x, _) -> x
      | XLambda(x, _, body) -> sprintf "(λ%s. %O)" x body
      | XApply(fn, arg, _) -> sprintf "(%O %O)" fn arg
      | XAnnot(exp, tpe) -> sprintf "(%O : %O)" exp tpe
      | XLet(v, exp, body) -> sprintf "let %s = %O in %O" v exp body
      | XIf(test, ift, iff) -> sprintf "if %O %O else %O" test ift iff

  /// Returns the type of the AST node `exprType`.
  let rec exprType = function
    | XUnit -> TUnit
    | XBool _ -> TBool
    | XVar(_, tpe) -> tpe
    | XLambda(_, atpe, body) -> TArrow(atpe, exprType body)
    | XApply(_, _, tpe) -> tpe
    | XAnnot(_, tpe) -> tpe
    | XLet(_, _, body) -> exprType body
    | XIf(_, _, fexp) -> exprType fexp

  /// Prints an AST along with type annotation information.
  let rec printTree expr indent =
    let nindent = indent + " "
    match expr with
    | XUnit ->
      printfn "%s() :: ()" indent
    | XBool b ->
      printfn "%s%b :: bool" indent b
    | XVar(name, tpe) ->
      printfn "%s%s :: %O" indent name tpe
    | XIf(test, ifT, ifF) ->
      printfn "%sif :: %O" indent (exprType expr)
      printTree test nindent
      printTree ifT nindent
      printTree ifF nindent
    | XLet(x, exp, body) ->
      printfn "%slet :: %O" indent (exprType expr)
      printfn "%s%s :: %O" nindent x (exprType exp)
      printTree exp  nindent
      printTree body nindent
    | XLambda(arg, atpe, exp) ->
      printfn "%sλ :: %O" indent (exprType expr)
      printfn "%s%s :: %O" nindent arg atpe
      printTree exp nindent
    | XApply(fn, arg, tpe) ->
      printfn "%s● :: %O" indent tpe
      printTree fn nindent
      printTree arg nindent
    | XAnnot(exp, ann) ->
      printfn "%s: :: %O" indent (exprType exp)
      printTree exp nindent
      printfn "%s %O" indent ann

  /// contexts (Γ,∆,Θ): · | Γ,α | Γ,x:A | Γ,â | Γ,â = τ | Γ,▶â
  type Note =
    | NUVar of string
    | NEVar of string
    | NAssump of string * Type
    | NSol of string * Type
    | NMark of string
    override this.ToString () =
      match this with
      | NUVar v -> "'"+v
      | NEVar v -> "^"+v
      | NAssump(v, tpe) -> sprintf "%s : %O" v tpe
      | NSol(v, tpe) -> sprintf "%s = %O" v tpe
      | NMark v -> "▶"+v

  // a context is an ordered list of notes (note: the head of the list is the most recently added
  // note, which is opposite the lexical representation in the paper)

  let private oneNote ctx w v p =
    match List.collect p ctx with
    | []   -> None
    | [at] -> Some at
    | ats  -> failwith (sprintf "Multiple %s for %s: %O" w v ats)

  /// Looks up the assumption for variable `v` in `ctx`.
  let assump ctx v =
    oneNote ctx "assumptions" v (function NAssump(av, at) when av = v -> [at] | _ -> [])

  /// Looks up the solution for existential variable `ev` in `ctx`.
  let solution ctx ev =
    oneNote ctx "solutions" ev (function NSol(sv, st) when sv = ev -> [st] | _ -> [])

  /// Peels off the end of a context up to and including `note`.
  let rec peel ctx note = match ctx with
                          | [] -> []
                          | h :: t when h = note -> t
                          | _ :: t -> peel t note

  let fmt ctx = ctx |> List.map (sprintf "%O") |> String.concat ", " |> sprintf "[%s]"

  /// Splits `ctx` into the part after `note` and the part before. `note` itself is not included.
  /// Recall that contexts list notes in reverse order, hence the `(post, pre)` return order.
  /// If `note` is not in `ctx` then `None` is returned.
  let split ctx note =
    let rec splitacc left = function
      | [] -> failwith (sprintf "Can't split %O on %O" ctx note)
      | h :: t when h = note -> (List.rev left, t)
      | h :: t -> splitacc (h :: left) t
    splitacc [] ctx

  /// Returns whether `eV` is in the free variables of `tpe`. */
  let rec containsFree tpe eV =
    match tpe with
    | TEVar v -> v = eV
    | TAll(_, tpe) -> containsFree tpe eV
    | TArrow(arg, res) -> (containsFree arg eV) || (containsFree res eV)
    | _ -> false

  let rec isMono tpe =
    match tpe with
    | TAll(_, _) -> false
    | TArrow(arg, res) -> (isMono arg) && (isMono res)
    | _ -> true

  let rec checkMalformed ctx tpe =
    match tpe with
    | TUnset -> None
    | TUnit -> None
    | TBool -> None
    | TUVar uv -> if List.contains (NUVar uv) ctx then None
                  else Some(sprintf "Unbound type variable '%s'" uv)
    | TEVar ev -> if (List.contains (NEVar ev) ctx) || (solution ctx ev |> Option.isSome) then None
                  else Some(sprintf "Unbound existential variable '%s'" ev)
    | TAll(uv, tpe)    -> checkMalformed (NUVar uv :: ctx) tpe
    | TArrow(arg, res) -> (checkMalformed ctx arg) |> Option.orElse (checkMalformed ctx res)

  let isWellFormed ctx tpe = not (Option.isSome (checkMalformed ctx tpe))

  let mutable nextEVar = 1
  let freshEVar name = try sprintf "%s%d" name nextEVar finally nextEVar <- nextEVar+1

  /// Applies `ctx` to `tpe` (substituting existential vars for their solutions).
  let rec apply ctx = function
    | TEVar ev as tev -> solution ctx ev |> Option.map (apply ctx) |> Option.defaultValue tev
    | TArrow(a, b)    -> TArrow(apply ctx a, apply ctx b)
    | TAll(uv,tpe)    -> TAll(uv, apply ctx tpe)
    | tpe             -> tpe

  let rec applyExpr ctx = function
    | XVar(v, tpe) -> XVar(v, apply ctx tpe)
    | XLambda(x, atpe, body) -> XLambda(x, apply ctx atpe, applyExpr ctx body)
    | XApply(fn, arg, tpe) -> XApply(applyExpr ctx fn, applyExpr ctx arg, apply ctx tpe)
    | XAnnot(exp, tpe) -> XAnnot(applyExpr ctx exp, apply ctx tpe)
    | XLet(x, exp, body) -> XLet(x, applyExpr ctx exp, applyExpr ctx body)
    | XIf(test, texp, fexp) -> XIf(applyExpr ctx test, applyExpr ctx texp, applyExpr ctx fexp)
    | exp -> exp

  /// Returns `arg` with `thatT` replaced by `thisT`.
  let rec subst thisT thatT = function
    | TUVar _ as uv -> if (thatT = uv) then thisT else uv
    | TArrow(a, b)  -> TArrow(subst thisT thatT a, subst thisT thatT b)
    | TAll(uv, tpe) -> TAll(uv, subst thisT thatT tpe)
    | tpe           -> tpe

  /// Instantiates `eA` such that `eA <: a` in `ctx`. See Figure 10.
  /// @return the output context. */
  let rec instantiateL ctx eA a =
    let neA = NEVar eA
    match a with
    // InstLSolve :: Γ,â,Γ′ ⊢ â :=< τ ⊣ Γ,â=τ,Γ′
    | a when (isMono a) && (isWellFormed (peel ctx neA) a) -> // Γ ⊢ τ
      let (postCtx, preCtx) = split ctx neA
      if (trace) then printfn "- InstLSolve %O :=< %O" eA a
      List.append postCtx ((NSol(eA, a) :: preCtx)) // Γ,â=τ,Γ′

    // InstLReach :: Γ[â][ĉ] ⊢ â :=< ĉ ⊣ Γ[â][ĉ=â]
    | TEVar eC when List.contains neA (peel ctx (NEVar eC)) ->
      let (postCtx, preCtx) = split ctx (NEVar eC)
      if (trace) then printfn "- InstLReach %O :=< %O" eA eC
      List.append postCtx (NSol(eC, (TEVar eA)) :: preCtx) // Γ[â][ĉ=â]

    // InstLArr :: Γ[â] ⊢ â :=< A1 → A2 ⊣ ∆
    | TArrow(a1, a2) when List.contains neA ctx ->
      let (postCtx, preCtx) = split ctx neA
      let eA1, eA2 = freshEVar "a₁", freshEVar "a₂"
      let neA1, teA1, neA2, teA2 = NEVar eA1, TEVar eA1, NEVar eA2, TEVar eA2
      let a1ctx = List.append postCtx (NSol(eA, TArrow(teA1, teA2)) :: neA1 :: neA2 :: preCtx)
      if (trace) then printfn "- InstLArr(1) %O :=< %O in %s" a1 eA1 (fmt a1ctx)
      let theta = instantiateR a1ctx a1 eA1 // Γ[â₂,â₁,â=â₁→â2] ⊢ A1 :=< â₁ ⊣ Θ
      if (trace) then printfn "- InstRArr(2) %O :=< %O in %s" eA2 (apply theta a2) (fmt theta)
      instantiateL theta eA2 (apply theta a2) // Θ ⊢ â₂ :=< [Θ]A2 ⊣ ∆

    // InstLAllR :: Γ[â] ⊢ â :=< ∀β.B ⊣ ∆
    | TAll(uB, b) when List.contains neA ctx ->
      let nuB = NUVar uB
      if (trace) then printfn "- InstLAllR %O :=< %O in %s" eA b (fmt (nuB :: ctx))
      let deltaEtc = instantiateL (nuB :: ctx) eA b // Γ[â],β ⊢ â :=< B ⊣ ∆,β,∆′
      peel deltaEtc nuB // ∆

    | _ -> failwith (sprintf "Failed to instantiate '%O' to '%O'" eA a)

  /// Instantiates `eA` such that `a <: eA` in `ctx`. See Figure 10.
  /// @return the output context.
  and instantiateR ctx a eA =
    let neA = NEVar eA
    match a with
    // InstRSolve :: Γ,â,Γ′ ⊢ τ :=< â ⊣ Γ,â=τ,Γ′
    | a when (isMono a) && (isWellFormed (peel ctx neA) a) -> // Γ ⊢ τ
      let (postCtx, preCtx) = split ctx neA
      if (trace) then printfn "- InstRSolve %O :=< %O" a eA
      List.append postCtx (NSol(eA, a) :: preCtx) // Γ,â=τ,Γ′

    // InstRReach :: Γ[â][ĉ] ⊢ ĉ :=< â ⊣ Γ[â][ĉ=â]
    | TEVar eC when List.contains neA (peel ctx (NEVar eC)) ->
      let (postCtx, preCtx) = split ctx (NEVar eC)
      if (trace) then printfn "- InstRReach %O :=< %O" eC eA
      List.append postCtx (NSol(eC, TEVar eA) :: preCtx) // Γ[â][ĉ = â]

    // InstRArr :: Γ[â] ⊢ A1 → A2 :=< â ⊣ ∆
    | TArrow(a1, a2) when List.contains neA ctx ->
      let (postCtx, preCtx) = split ctx neA
      let eA1, eA2 = freshEVar("a₁"), freshEVar("a₂")
      let neA1, teA1, neA2, teA2 = NEVar eA1, TEVar eA1, NEVar eA2, TEVar eA2
      let a1ctx = List.append postCtx (NSol(eA, TArrow(teA1, teA2)) :: neA1 :: neA2 :: preCtx)
      if (trace) then printfn "- InstRArr(1) %O :=< %O in %s" eA1 a1 (fmt a1ctx)
      let theta = instantiateL a1ctx eA1 a1 // Γ[â₂,â₁,â=â₁→â₂] ⊢ â₁ :=< A1 ⊣ Θ
      if (trace) then printfn "- InstRArr(2) %O :=< %O in %s" (apply theta a2) eA2 (fmt theta)
      instantiateR theta (apply theta a2) eA2 // Θ ⊢ [Θ]A2 :=< â₂ ⊣ ∆

    // InstRAllL :: Γ[â],▶ĉ,ĉ ⊢ [ĉ/β]B :=< â ⊣ ∆,▶ĉ,∆′
    | TAll(uB, b) when List.contains neA ctx ->
      let eC = freshEVar("c")
      let instCtx = (NEVar eC) :: (NMark eC) :: ctx // Γ[â],▶ĉ,ĉ
      if (trace) then printfn "- InstRAllL [%O/%O]%O :=< %O in %s" eC uB b eA (fmt instCtx)
      let bSubst = subst (TEVar eC) (TUVar uB) b
      let deltaEtc = instantiateR instCtx bSubst eA // Γic ⊢ [ĉ/β]B :=< â ⊣ ∆,▶ĉ,∆′
      peel deltaEtc (NMark eC) // ∆

    | _ -> failwith (sprintf "Failed to instantiate '%O' to '%O'\n (context: %O)" a eA ctx)

  /// Derives a subtyping relationship `tpeA <: tpeB` with input context `ctx`. See Figure 9.
  /// @return the output context.
  let rec subtype ctx tpeA tpeB =
    // <:Unit :: Γ ⊢ 1 <: 1 ⊣ Γ
    match (tpeA, tpeB) with
    | (TUnit, TUnit) -> ctx
    | (TBool, TBool) -> ctx
    // <:Var :: Γ[α] ⊢ α <: α ⊣ Γ[α]
    | (TUVar _, TUVar _) when (tpeA = tpeB) -> ctx // Γ
    // <:Exvar :: Γ[â] ⊢ â <: â ⊣ Γ[â]
    | (TEVar eA, TEVar _) when (tpeA = tpeB) ->
      if (List.contains (NEVar eA) ctx) then ctx // Γ
      else failwith (sprintf "Unbound existential '%O'" tpeA)
    // <:→ :: Γ ⊢ A1→A2 <: B1→B2 ⊣ ∆
    | (TArrow(a1, a2), TArrow(b1, b2)) ->
      let theta = subtype ctx b1 a1 // Γ ⊢ B1 <: A1 ⊣ Θ
      subtype theta (apply theta a2) (apply theta b2) // Θ ⊢ [Θ]A2 <: [Θ]B2 ⊣ ∆
    // <:∀L :: Γ ⊢ ∀α.A <: B ⊣ ∆
    | (TAll(uA, a), b) ->
      let eA = freshEVar "a"
      let eAMark = NMark(eA)
      let subCtx = NEVar(eA) :: eAMark :: ctx // Γ,▶â,â
      let deltaEtc = subtype subCtx (subst (TEVar eA) (TUVar uA) a) b // [â/α]A <: B ⊣ ∆,▶â,Θ
      peel deltaEtc eAMark // ∆
    // <:∀R :: Γ ⊢ A <: ∀α.B ⊣ ∆
    | (a, TAll(uA, b)) ->
      let nuA = NUVar uA
      let deltaEtc = subtype (nuA :: ctx) a b // Γ,α ⊢ A <: B ⊣ ∆,α,Θ
      peel deltaEtc nuA // ∆
    // <:InstantiateL :: Γ[â] ⊢ â <: A ⊣ ∆
    | (TEVar eA, a) when (List.contains (NEVar eA) ctx) && not (containsFree a eA) ->
      if (trace) then printfn "- <:InstL %O :=< %O" eA a
      instantiateL ctx eA a // Γ[â] ⊢ â :=< A ⊣ ∆
    // <:InstantiateR :: Γ[â] ⊢ A <: â ⊣ ∆
    | (a, TEVar eA) when (List.contains (NEVar eA) ctx) && not (containsFree a eA) ->
      if (trace) then printfn "- <:InstR %O :=< %O" a eA
      instantiateR ctx a eA // Γ[â] ⊢ A <: â ⊣ ∆
    | _ -> failwith (sprintf "Type mismatch: expected '%O', given: '%O'" tpeB tpeA)


  /// Checks that `exp` has type `tpe` with input context `ctx`. See Figure 11.
  /// @return the term with type assigned, and the output context.
  let rec check ctx exp tpe =
    match (exp, tpe) with
    // 1I :: ((), 1)
    | (XUnit, TUnit) -> (exp, ctx) // Γ
    // TI :: (T/F, Bool)
    | (XBool _, TBool) -> (exp, ctx) // Γ

    // ->I :: (λx.e, A→B)
    | (XLambda(arg, _, body), TArrow(argT, bodyT)) ->
      // exp.tpe = tpe  // lambda types are not always synthesized, so we also assign lambda AST
      // arg.tpe = argT // nodes a type during checking, ditto for the lambda argument nodes
      let argAssump = NAssump(arg, argT) // x:A
      if (trace) then printfn "- ->I (%O <= %O) in %s" body bodyT (fmt (argAssump :: ctx))
      let (checkedBody, deltaEtc) = check (argAssump :: ctx) body bodyT // Γ,x:A ⊢ e ⇐ B ⊣ ∆,x:A,Θ
      let delta = peel deltaEtc argAssump // ∆
      (XLambda(arg, argT, checkedBody), delta)

    // ∀I :: (e, ∀α.A)
    | (exp, TAll(uA, tpe)) ->
      let nuA = NUVar uA
      if (trace) then printfn "- ∀I (%O <= %O) in %s" exp tpe (fmt (nuA :: ctx))
      let (checkedExp, deltaEtc) = check (nuA :: ctx) exp tpe // Γ,α ⊢ e ⇐ A ⊣ ∆,α,Θ
      (checkedExp, peel deltaEtc nuA) // ∆

    // If :: (if test ifTrue else ifFalse, T)
    | (XIf(test, ifTrue, ifFalse), tpe) ->
      // exp.tpe = tpe
      if (trace) then printfn "- If (%O <= Bool) in %s" test (fmt ctx)
      let (checkedTest, _) = check ctx test TBool
      if (trace) then printfn "- If (%O <= %O) in %s" ifTrue tpe (fmt ctx)
      let (checkedTrue, _) = check ctx ifTrue tpe
      if (trace) then printfn "- If (%O <= %O) in %s" ifFalse tpe (fmt ctx)
      let (checkedFalse, delta) = check ctx ifFalse tpe
      (XIf(checkedTest, checkedTrue, checkedFalse), delta) // peel delta?

    // Sub :: (e, B)
    | (exp, tpe) ->
      let (expType, checkedExp, theta) = infer ctx exp // Γ ⊢ e ⇒ A ⊣ Θ
      if (trace) then printfn "- Sub (%O -> %O) ; [Θ]%O <: [Θ]%O in %s" exp expType expType tpe (fmt theta)
      let delta = subtype theta (apply theta expType) (apply theta tpe)
      // apply the solutions from subtyping to our subtree, otherwise we can be left with temporary
      // type variables in type checked subtrees
      (applyExpr delta checkedExp, delta) // Θ ⊢ [Θ]A <: [Θ]B ⊣ ∆

  /// Infers a type for `exp` with input context `ctx`. See Figure 11.
  /// @return the inferred type, the term with type assigned, and the output context.
  and infer ctx exp =
    match exp with
    // 1I=> :: ()
    | XUnit -> (TUnit, exp, ctx) // 1 ⊣ Γ
    // BoolI=> :: T/F
    | XBool _ -> (TBool, exp, ctx) // Bool ⊣ Γ

    // Var :: x
    | XVar(name, _) ->
      match assump ctx name with
      | Some(tpe) -> (tpe, XVar(name, tpe), ctx) // A ⊣ Γ
      | None      -> failwith (sprintf "No binding for variable '%s'" name)
    // Let-> :: let x = exp in body
    | XLet(x, exp, body) ->
      let (expType, inferredExp, theta) = infer ctx exp
      let eC = freshEVar("c")
      let teC = TEVar eC
      let assump = NAssump(x, expType)
      // x.tpe = expType // assign type to var node, which is not separately entyped
      let checkCtx = assump :: (NEVar eC) :: theta
      if (trace) then printfn "- Let-> (%O <= %O) in %s" body eC (fmt checkCtx)
      let (checkedBody, checkedCtx) = check checkCtx body teC
      (teC, XLet(x, inferredExp, checkedBody), peel checkedCtx assump)
    // If=> :: if test ifTrue else ifFalse
    | XIf(test, ifTrue, ifFalse) ->
      let (checkedTest, _) = check ctx test TBool
      let (trueType, inferredTrue, theta) = infer ctx ifTrue
      if (trace) then printfn "- If-> ('%O' -> %O) ; ('%O' <= %O) in %s" ifTrue trueType ifFalse trueType (fmt theta)
      let (checkedFalse, delta) = check theta ifFalse trueType
      (trueType, XIf(checkedTest, inferredTrue, checkedFalse), delta) // TODO: peel?
    // ->I=> :: λx.e
    | XLambda(arg, _, body) ->
      let eA, eC = freshEVar("a"), freshEVar("c") // â, ĉ
      let teA, teC = TEVar eA, TEVar eC
      let assump = NAssump(arg, teA) // x:â
      // arg.tpe = eA // assign type to arg node, which is not separately entyped
      let checkCtx = assump :: (NEVar eC) :: (NEVar eA) :: ctx // Γ,â,ĉ,x:â
      if (trace) then printfn "- ->I=> ('%O' <= %O) in %s" body eC (fmt checkCtx)
      let (checkedBody, checkedCtx) = check checkCtx body teC // e ⇐ ĉ ⊣ ∆,x:â,Θ
      (TArrow(teA, teC), XLambda(arg, teA, checkedBody), peel checkedCtx assump) // â→ĉ ⊣ ∆
    // ->E :: (e1 e2)
    | XApply(fn, arg, _) ->
      let (funType, checkedFun, theta) = infer ctx fn // e1 ⇒ A ⊣ Θ
      let reducedFun = apply theta funType // [Θ]A
      if (trace) then printfn "- ->E '%O' -> %O ; %O ● '%O' in %s" fn funType reducedFun arg (fmt theta)
      let (resType, checkedArg, delta) = inferApp theta reducedFun arg // C ⊣ ∆
      // fn.apply(delta)
      (resType, XApply(checkedFun, checkedArg, resType), delta)
    // Anno: x:A
    | XAnnot(x, ann) ->
      // ann.checkWellFormed
      let (checkedExp, delta) = check ctx x ann
      (ann, checkedExp, delta) // A ⊣ ∆

  /// Infers the type of an application of a function of type `fun` to `exp`. See Figure 11.
  /// @return the inferred type, the term with type assigned, and the output context.
  and inferApp ctx fn exp =
    match fn with
    // ∀App
    | TAll(uv, tpe) ->
      let eA = freshEVar("a") // â
      let reduced = subst (TEVar eA) (TUVar uv) tpe // [â/α]A
      let appCtx = (NEVar eA) :: ctx // Γ,â
      if (trace) then printfn "- ∀App %O ● '%O' in %s" reduced exp (fmt appCtx)
      inferApp appCtx reduced exp // C ⊣ ∆
    // âApp
    | TEVar eA ->
      let a1 = freshEVar("a₁") // â₁
      let a2 = freshEVar("a₂") // â₂
      let aArrow = TArrow(TEVar a1, TEVar a2) // â₁→â₂
      let (postCtx, preCtx) = split ctx (NEVar eA) // Γpre[â]post
      let checkCtx = List.append postCtx (NSol(eA, aArrow) :: (NEVar a1) :: (NEVar a2) :: preCtx) // Γpre[â₂,â₁,â=â₁→â₂]post
      if (trace) then printfn "- âApp '%O' <= %O in %s" exp a1 (fmt checkCtx)
      let (checkedExp, delta) = check checkCtx exp (TEVar a1)
      (TEVar a2, checkedExp, delta) // â₂ ⊣ ∆
    // ->App
    | TArrow(argT, resT) -> // A→C
      let (checkedExp, delta) = check ctx exp argT
      (resT, checkedExp, delta) // C ⊣ ∆
    // <fail>
    | fn -> failwith (sprintf "Cannot apply expr of type '%O' to '%O'" fn exp)

  /// Runs inference on `expr` and returns the term with type assigned or throws an error.
  let inferExpr expr =
    nextEVar <- 1 // makes error messages less arbitrary
    if (trace) then printfn "inferExpr %O" expr
    let (_, infExpr, delta) = infer [] expr
    if (trace) then printfn "∆ = %O" delta
    if (trace) then printTree infExpr ""
    // apply the final context to the top-level term, which will have only been inferred and not
    // checked (checking is where we normally apply contexts)
    applyExpr delta infExpr
