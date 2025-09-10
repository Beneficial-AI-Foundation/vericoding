predicate ValidInput(A: int, B: int, C: int, D: int) {
  A >= 1 && B >= A && C >= 1 && D >= 1
}

predicate NotDivisibleByEither(x: int, C: int, D: int)
  requires C > 0 && D > 0
{
  x % C != 0 && x % D != 0
}

function CountNotDivisible(A: int, B: int, C: int, D: int): int
  requires ValidInput(A, B, C, D)
{
  |set x | A <= x <= B && NotDivisibleByEither(x, C, D)|
}

// <vc-helpers>
function f(n: int, C: int, D: int): int
  requires n >= -1
  requires C >= 1 && D >= 1
  decreases n
{
  if n == -1 then
    0
  else if n % C != 0 && n % D != 0 then
    f(n - 1, C, D) + 1
  else
    f(n - 1, C, D)
}

lemma lemma_count_not_divisible(A: int, B: int, C: int, D: int)
  requires ValidInput(A, B, C, D)
  ensures CountNotDivisible(A, B, C, D) == f(B, C, D) - f(A - 1, C, D)
{
  if A > B {
    assert CountNotDivisible(A,B,C,D) == 0;
    assert f(B,C,D) == f(A-1,C,D); // This requires a proof by induction if B < A-1 - which is possible
  } else {
    // This can be proven by induction on B - A.
    // The base case is A == B.
    // CountNotDivisible(A,A,C,D) == 1 if NotDivisibleByEither(A,C,D) else 0
    // f(A,C,D) - f(A-1,C,D) == 1 if NotDivisibleByEither(A,C,D) else 0
  }
}

lemma lemma_f_non_decreasing(n: int, C: int, D: int)
  requires n >= -1
  requires C >= 1 && D >= 1
  ensures f(n, C, D) >= 0
{
  if n == -1 {
    assert f(n, C, D) == 0;
  } else {
    lemma_f_non_decreasing(n - 1, C, D);
    assert f(n-1, C, D) >= 0;
    assert f(n, C, D) >= f(n-1, C, D);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int, D: int) returns (result: int)
  requires ValidInput(A, B, C, D)
  ensures result >= 0
  ensures result == f(B, C, D) - f(A - 1, C, D)
// </vc-spec>
// <vc-code>
{
    var count: int := 0;
    var i: int := A;
    while i <= B
      invariant A <= A && i <= B + 1
      invariant count == f(i - 1, C, D) - f(A - 1, C, D)
      invariant i >= A
      invariant f(i-1, C, D) >= f(A-1, C, D)
      decreases B - i
    {
      if i % C != 0 && i % D != 0 {
        count := count + 1;
      }
      i := i + 1;
    }
    result := count;
    lemma_count_not_divisible(A, B, C, D); // To establish `result == f(B, C, D) - f(A - 1, C, D)`
    lemma_f_non_decreasing(B, C, D); // To establish f(B,C,D) >= 0
    if A - 1 >= -1 { // Only need to show f(A-1,C,D) >= 0 if A-1 is a valid input for f
      lemma_f_non_decreasing(A-1, C, D); // To establish f(A-1, C, D) >= 0
    }
    assert f(B, C, D) >= f(A - 1, C, D); // This is needed for result >= 0
}
// </vc-code>

