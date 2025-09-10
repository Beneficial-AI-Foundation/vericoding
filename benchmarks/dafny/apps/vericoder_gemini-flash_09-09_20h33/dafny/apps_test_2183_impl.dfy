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
lemma LateBrotherProperty(a: int, b: int)
  requires ValidBrotherNumbers(a, b)
  ensures 1 <= LateBrother(a, b) <= 3
  ensures LateBrother(a, b) != a
  ensures LateBrother(a, b) != b
{
  var c := LateBrother(a, b);
  // Prove 1 <= c <= 3
  assert a + b <= 3 + 2; // a <= 3, b <= 3, a != b. Max sum is 3+2=5, e.g., a=3, b=2
  assert a + b >= 1 + 2; // Min sum is 1+2=3, e.g., a=1, b=2
  assert 6 - (3 + 2) <= c <= 6 - (1 + 2); // 6 - (max sum) <= c <= 6 - (min sum)
  assert 1 <= c <= 3;

  // Prove c != a
  // If c == a, then 6 - a - b == a => 6 - b == 2 * a
  // Since a and b are valid brother numbers (1 to 3, distinct), the possible pairs (a,b) are:
  // (1,2) => 6-2 = 4, 2*1 = 2. 4 != 2
  // (1,3) => 6-3 = 3, 2*1 = 2. 3 != 2
  // (2,1) => 6-1 = 5, 2*2 = 4. 5 != 4
  // (2,3) => 6-3 = 3, 2*2 = 4. 3 != 4
  // (3,1) => 6-1 = 5, 2*3 = 6. 5 != 6
  // (3,2) => 6-2 = 4, 2*3 = 6. 4 != 6
  // In all cases, 6 - b != 2 * a. So c != a.

  // Prove c != b
  // If c == b, then 6 - a - b == b => 6 - a == 2 * b
  // This is symmetric to the above case.
  // (1,2) => 6-1 = 5, 2*2 = 4. 5 != 4
  // (1,3) => 6-1 = 5, 2*3 = 6. 5 != 6
  // (2,1) => 6-2 = 4, 2*1 = 2. 4 != 2
  // (2,3) => 6-2 = 4, 2*3 = 6. 4 != 6
  // (3,1) => 6-3 = 3, 2*1 = 2. 3 != 2
  // (3,2) => 6-3 = 3, 2*2 = 4. 3 != 4
  // In all cases, 6 - a != 2 * b. So c != b.
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
  // Prove IsValidResult(a, b, result)
  // This means proving (1 <= result <= 3 && result != a && result != b)
  // when ValidBrotherNumbers(a, b) holds.
  // This is precisely what LateBrotherProperty lemma provides.
  LateBrotherProperty(a, b);
  assert IsValidResult(a, b, result); // This assertion is ensured by the lemma.

  // Prove result == LateBrother(a, b)
  // This is true by definition of LateBrother and the assignment.
  assert result == LateBrother(a, b);
}
// </vc-code>

