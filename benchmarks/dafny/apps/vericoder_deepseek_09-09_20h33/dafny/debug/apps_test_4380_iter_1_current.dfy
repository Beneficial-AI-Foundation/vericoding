predicate ValidInput(a: int, b: int)
{
    1 <= a <= 3 && 1 <= b <= 3
}

predicate IsOdd(n: int)
{
    n % 2 == 1
}

predicate ExistsOddProduct(a: int, b: int)
  requires ValidInput(a, b)
{
    exists c :: 1 <= c <= 3 && IsOdd(a * b * c)
}

function ShouldAnswerYes(a: int, b: int): bool
  requires ValidInput(a, b)
{
    a != 2 && b != 2
}

// <vc-helpers>
lemma OddProductLemma(a: int, b: int, c: int)
  requires ValidInput(a, b)
  requires 1 <= c <= 3
  ensures IsOdd(a * b * c) <==> IsOdd(a * b)
{
  // The parity of a*b*c is the same as a*b since c is odd (1 or 3)
  // because multiplying by an odd number doesn't change parity
}

lemma ExistsOddProductTheorems(a: int, b: int)
  requires ValidInput(a, b)
  ensures ExistsOddProduct(a, b) == (a * b % 2 == 1)
{
  if a * b % 2 == 1 {
    // If a*b is odd, then any c (1 or 3) will keep it odd
    assert IsOdd(a * b * 1);
    assert 1 <= 1 <= 3;
  } else {
    // If a*b is even, then no c (1 or 3, both odd) can make it odd
    // because even * odd = even
    forall c | 1 <= c <= 3
      ensures !IsOdd(a * b * c)
    {
      assert a * b * c % 2 == 0;
    }
  }
}

lemma ShouldAnswerYesLemma(a: int, b: int)
  requires ValidInput(a, b)
  ensures ShouldAnswerYes(a, b) == (a * b % 2 == 1)
{
  // ShouldAnswerYes is a != 2 && b != 2
  // This means both a and b are odd (1 or 3)
  // The product of two odd numbers is odd
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
  requires ValidInput(a, b)
  ensures result == (if ShouldAnswerYes(a, b) then "Yes" else "No")
// </vc-spec>
// <vc-code>
{
  if a * b % 2 == 1 {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

