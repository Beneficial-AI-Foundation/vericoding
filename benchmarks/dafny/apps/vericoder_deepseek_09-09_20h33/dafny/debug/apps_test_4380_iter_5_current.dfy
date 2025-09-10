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
  assert c == 1 || c == 2 || c == 3;
  if c == 2 {
    assert a * b * c == a * b * 2;
    assert a * b * 2 % 2 == 0;  // Explicitly state that multiplying by 2 makes it even
    assert !IsOdd(a * b * 2);
  } else {
    assert IsOdd(c);
    // Multiplying by odd preserves parity
    assert (a * b * c) % 2 == (a * b) % 2;
  }
}

lemma ExistsOddProductTheorems(a: int, b: int)
  requires ValidInput(a, b)
  ensures ExistsOddProduct(a, b) == (a * b % 2 == 1)
{
  if a * b % 2 == 1 {
    // If a*b is odd, then any odd c (1 or 3) will keep it odd
    assert IsOdd(a * b * 1);
    assert 1 <= 1 <= 3;
  } else {
    // If a*b is even, then no odd c (1 or 3) can make it odd
    // because even * odd = even
    forall c | 1 <= c <= 3 && c != 2
      ensures !IsOdd(a * b * c)
    {
      // c is odd (1 or 3), so even * odd = even
      assert c == 1 || c == 3;
      assert IsOdd(c);
      assert (a * b * c) % 2 == (a * b) % 2 == 0;
    }
    // Explicitly handle c=2 case
    assert !IsOdd(a * b * 2);
  }
}

lemma ShouldAnswerYesLemma(a: int, b: int)
  requires ValidInput(a, b)
  ensures ShouldAnswerYes(a, b) == (a * b % 2 == 1)
{
  match (a, b) {
    case (1, 1) => assert a * b % 2 == 1; 
    case (1, 3) => assert a * b % 2 == 1;
    case (3, 1) => assert a * b % 2 == 1;
    case (3, 3) => assert a * b % 2 == 1;
    case (1, 2) => assert a * b % 2 == 0;
    case (2, 1) => assert a * b % 2 == 0;
    case (2, 3) => assert a * b % 2 == 0;
    case (3, 2) => assert a * b % 2 == 0;
    case (2, 2) => assert a * b % 2 == 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
  requires ValidInput(a, b)
  ensures result == (if ShouldAnswerYes(a, b) then "Yes" else "No")
// </vc-spec>
// <vc-code>
{
  if ShouldAnswerYes(a, b) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

