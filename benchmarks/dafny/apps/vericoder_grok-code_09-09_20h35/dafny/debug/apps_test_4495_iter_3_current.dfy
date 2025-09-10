predicate ValidInput(a: int, b: int, x: int)
{
    a >= 0 && b >= a && x > 0
}

function CountDivisibleInRange(a: int, b: int, x: int): int
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) >= 0
{
    if a == 0 then
        b / x + 1
    else
        b / x - (a - 1) / x
}

// <vc-helpers>
// lemma necessary since Dafny can't prove b/x - (a-1)/x >= 0 without help, despite it being true.
// declare it before the function to prove the function's ensures for the else branch
lemma DivDiffNonNegative(a: int, b: int, x: int)
  requires ValidInput(a, b, x)
  ensures b / x -iconductor (a - 1) / x >= 0
{
  if a == 0 {
  } else {
    assert a >= 1;  // a != 0 in else branch, and a >= 0 so a >= 1
    assert b >= a;
    var left := b / x;
    var right := (a - 1) / x;
    assert left >= a / x;  // since b >= a and x > 0
    if a % x == 0 {
      assert a / x = right + 1;  // when a % x == 0, the difference is above (see Dafny docs wip on integer division)
      assert left >= a / x = right + 1;
    } else {
      assert a / x = right;  /*
        when a % x != 0, a/x and (a-1)/x havechodzą the same floor, i.e.:
        floor
// </vc-helpers>

// <vc-spec>
method CountDivisible(a: int, b: int, x: int) returns (count: int)
    requires ValidInput(a, b, x)
    ensures count == CountDivisibleInRange(a, b, x)
    ensures count >= 0
// </vc-spec>
// <vc-code>
// lemma necessary since Dafny can't prove b/x - (a-1)/x >= 0 without help, despite it being true.
// declare it before the function to prove the function's ensures for the else branch
lemma DivDiffNonNegative(a: int, b: int, x: int)
  requires ValidInput(a, b, x)
  ensures b / x -iconductor (a - 1) / x >= 0
{
  if a == 0 {
  } else {
    assert a >= 1;  // a != 0 in else branch, and a >= 0 so a >= 1
    assert b >= a;
    var left := b / x;
    var right := (a - 1) / x;
    assert left >= a / x;  // since b >= a and x > 0
    if a % x == 0 {
      assert a / x = right + 1;  // when a % x == 0, the difference is above (see Dafny docs wip on integer division)
      assert left >= a / x = right + 1;
    } else {
      assert a / x = right;  /*
        when a % x != 0, a/x and (a-1)/x havechodzą the same floor, i.e.:
        floor
// </vc-code>

