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
lemma LateBrotherCorrect(a: int, b: int)
  requires ValidBrotherNumbers(a, b)
  ensures 1 <= LateBrother(a, b) <= 3
  ensures LateBrother(a, b) != a
  ensures LateBrother(a, b) != b
{
  var result := LateBrother(a, b);
  assert result == 6 - a - b;
  
  // Since a and b are distinct values from {1, 2, 3}, their sum is either 3, 4, or 5
  // So 6 - (a + b) is either 3, 2, or 1
  assert a + b == 3 || a + b == 4 || a + b == 5;
  
  if a + b == 3 {
    assert (a == 1 && b == 2) || (a == 2 && b == 1);
    assert result == 3;
  } else if a + b == 4 {
    assert (a == 1 && b == 3) || (a == 3 && b == 1);
    assert result == 2;
  } else {
    assert a + b == 5;
    assert (a == 2 && b == 3) || (a == 3 && b == 2);
    assert result == 1;
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
  LateBrotherCorrect(a, b);
}
// </vc-code>

