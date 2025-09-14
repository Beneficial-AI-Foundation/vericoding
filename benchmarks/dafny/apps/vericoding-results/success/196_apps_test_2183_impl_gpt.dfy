predicate ValidBrotherNumbers(a: int, b: int)
{
  1 <= a <= 3 && 1 <= b <= 3 && a != b
}

function LateBrother(a: int, b: int): int
  requires ValidBrotherNumbers(a, b)
{
  6 - a - b
}

predicate IsValidResult(a: int, b: int, result: int)
{
  ValidBrotherNumbers(a, b) ==> 
    (1 <= result <= 3 && result != a && result != b)
}

// <vc-helpers>
lemma LateBrotherIsValid(a: int, b: int)
  requires ValidBrotherNumbers(a, b)
  ensures IsValidResult(a, b, LateBrother(a, b))
{
  if a == 1 {
    if b == 2 {
      assert LateBrother(a, b) == 3;
    } else if b == 3 {
      assert LateBrother(a, b) == 2;
    } else {
      assert false;
    }
  } else if a == 2 {
    if b == 1 {
      assert LateBrother(a, b) == 3;
    } else if b == 3 {
      assert LateBrother(a, b) == 1;
    } else {
      assert false;
    }
  } else if a == 3 {
    if b == 1 {
      assert LateBrother(a, b) == 2;
    } else if b == 2 {
      assert LateBrother(a, b) == 1;
    } else {
      assert false;
    }
  } else {
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidBrotherNumbers(a, b)
  ensures IsValidResult(a, b, result)
  ensures result == LateBrother(a, b)
// </vc-spec>
// <vc-code>
{
  result := LateBrother(a, b);
  LateBrotherIsValid(a, b);
}
// </vc-code>

