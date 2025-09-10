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
  // Since a and b are distinct integers from {1, 2, 3}, their sum (a + b) can be:
  // 1+2 = 3
  // 1+3 = 4
  // 2+3 = 5
  //
  // Thus, 6 - (a + b) will be:
  // 6 - 3 = 3
  // 6 - 4 = 2
  // 6 - 5 = 1
  //
  // Therefore, 1 <= LateBrother(a, b) <= 3 holds.
  //
  // To prove LateBrother(a, b) != a:
  // Assume LateBrother(a, b) == a
  // 6 - a - b == a
  // 6 - b == 2 * a
  // This implies 2*a is either 6-1=5, 6-2=4, 6-3=3
  // So 2*a is even (4) or odd (3,5)
  // If 2*a = 4, then a = 2.
  //   In this case, 6-b = 4, so b = 2. But a != b is given. Contradiction.
  // If 2*a = 3 or 2*a = 5, then a is not an integer. Contradiction.
  // Therefore, LateBrother(a, b) != a.
  //
  // By symmetry, LateBrother(a, b) != b.
  // (6 - a - b == b  =>  6 - a == 2 * b. Similar contradiction.)
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
  var c := LateBrother(a, b);
  // Prove ensures IsValidResult(a, b, result)
  // Which expands to ValidBrotherNumbers(a, b) ==> (1 <= result <= 3 && result != a && result != b)

  // We are given requires ValidBrotherNumbers(a, b).
  // So we need to show (1 <= c <= 3 && c != a && c != b).
  // This is exactly what the LateBrotherProperty lemma proves about LateBrother(a, b).
  LateBrotherProperty(a, b);

  result := c;
}
// </vc-code>

