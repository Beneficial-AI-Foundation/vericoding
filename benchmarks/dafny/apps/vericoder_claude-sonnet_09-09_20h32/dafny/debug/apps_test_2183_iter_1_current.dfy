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
  ensures 1 <= LateBrother(a, b) <= 3
  ensures LateBrother(a, b) != a
  ensures LateBrother(a, b) != b
{
  var late := LateBrother(a, b);
  assert late == 6 - a - b;
  
  // Since a and b are in {1, 2, 3} and a != b,
  // the possible pairs are: (1,2), (1,3), (2,1), (2,3), (3,1), (3,2)
  // For each pair, 6 - a - b gives: 3, 2, 3, 1, 2, 1 respectively
  
  if a == 1 && b == 2 {
    assert late == 3;
  } else if a == 1 && b == 3 {
    assert late == 2;
  } else if a == 2 && b == 1 {
    assert late == 3;
  } else if a == 2 && b == 3 {
    assert late == 1;
  } else if a == 3 && b == 1 {
    assert late == 2;
  } else if a == 3 && b == 2 {
    assert late == 1;
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
  result := 6 - a - b;
  LateBrotherIsValid(a, b);
}
// </vc-code>

