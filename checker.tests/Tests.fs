module Tests

open System
open Xunit
open checker.Bidir

[<Fact>]
let testPeel () =
  let ctx = [NUVar "b"; NUVar "a"; NEVar "c"]
  let expect = [NEVar "c"]
  let got = peel ctx (NUVar "a")
  Assert.Equal<Note list>(expect, got)

[<Fact>]
let testAssump () =
  let ctx = [NUVar "b"; NAssump("c", TBool); NEVar "c"]
  let expect = [NEVar "c"]
  let got = peel ctx (NAssump("c", TBool))
  Assert.Equal<Note list>(expect, got)

let xV = XVar("x", TUnset)
let yV = XVar("y", TUnset)
let fV = XVar("f", TUnset)
let aTV = TUVar("a")
let xTrue = XBool false
let xFalse = XBool false

// id :: (forall a. a -> a)
let idType = TAll("a", TArrow(aTV, aTV))
// id x = x
let idExpr = XLambda("x", TUnset, xV)

[<Fact>]
let testIdent () =
  let expr = XAnnot(XLambda("x", TUnset, xV), idType)
  let infExpr = inferExpr expr
  // printTree infExpr ""
  Assert.Equal(TArrow(aTV, aTV), exprType infExpr) // TODO: is this desirable?
  Assert.Equal(TArrow(TEVar "a1", TEVar "a1"), idExpr |> inferExpr |> exprType)
  Assert.Equal(TUnit, XApply(idExpr, XUnit, TUnset) |> inferExpr |> exprType)

// hof :: (forall a. () -> a) -> a
// hof f = f ()
let hofUnitExpr = XLambda("f", TUnset, XApply(fV, XUnit, TUnset))
// hof :: (forall a. Bool -> a) -> a
// hof f = f true
let hofBoolExpr = XLambda("f", TUnset, XApply(fV, XBool true, TUnset))

[<Fact>]
let testHOF () =
  let boolExpr = inferExpr (XApply(hofBoolExpr, idExpr, TUnset))
  // printTree infExpr ""
  Assert.Equal(TBool, exprType boolExpr)
  let unitExpr = inferExpr (XApply(hofUnitExpr, idExpr, TUnset))
  // printTree unitExpr ""
  Assert.Equal(TUnit, exprType unitExpr)

let inferFailure expr =
  try inferExpr expr |> ignore ; "<failed to fail!>"
  with
  | Failure msg -> msg

[<Fact>]
let testError () =
  let errMsg = inferFailure (XApply(hofUnitExpr, XUnit, TUnset))
  Assert.Equal("Type mismatch: expected '() → ^a₂4', given: '()'", errMsg)

// hrf :: (forall a. (a -> a)) -> ()
let hrfType = TArrow(TAll("a", TArrow(aTV, aTV)), TUnit)
// hrf f = (f id) (f ())
let hrfExpr = XLambda("f", TUnset, XApply(XApply(fV, idExpr, TUnset),
                                          XApply(fV, XUnit, TUnset), TUnset))

[<Fact>]
let testHigherRank () =
  // fail: cannot infer higher-rank types
  Assert.Equal("Type mismatch: expected '^a₂8 → ^a₂8', given: '()'", inferFailure hrfExpr)
  let hrfAnnot = XAnnot(hrfExpr, hrfType) // (hrf : hrfType)
  let hrfAnnotExpr = hrfAnnot |> inferExpr
  // printTree hrfAnnotExpr ""
  Assert.Equal(hrfType, hrfAnnotExpr |> exprType)
  let hrfAppExpr = XApply(hrfAnnot, idExpr, TUnset) |> inferExpr
  // printTree hrfAppExpr ""
  Assert.Equal(TUnit, hrfAppExpr |> exprType) // ((hrf : hrfType) id)

[<Fact>]
let testLet () =
  // let y = (λx.x) false in y
  Assert.Equal(TBool, XLet("y", XApply(idExpr, xFalse, TUnset), yV) |> inferExpr |> exprType)
  // let y = (λx.x) in (y false)
  Assert.Equal(TBool, XLet("y", idExpr, XApply(yV, xFalse, TUnset)) |> inferExpr |> exprType)
  // let f = (λx.x) in let y = (λx.x) in ((f y) false)
  let yLetE = XLet("y", idExpr, XApply(XApply(fV, yV, TUnset), xFalse, TUnset))
  Assert.Equal(TBool, XLet("f", idExpr, yLetE) |> inferExpr |> exprType)
  // let f = (λx.x) : (forall a. a -> a) in let y = (λx.x) in ((f y) (f false))
  let yLetU = XLet("y", idExpr, XApply(XApply(fV, yV, TUnset), XApply(fV, xFalse, TUnset), TUnset))
  let expr = XLet("f", XAnnot(idExpr, idType), yLetU) |> inferExpr
  // printfn "%O" expr
  // printTree expr ""
  Assert.Equal(TBool, expr |> exprType)

