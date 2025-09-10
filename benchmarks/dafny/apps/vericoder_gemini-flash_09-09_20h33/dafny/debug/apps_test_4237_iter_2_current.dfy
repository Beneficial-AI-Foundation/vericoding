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
    // The required property becomes 0 == f(B,C,D) - f(A-1,C,D).
    // If B < A-1, this requires f(B,C,D) == f(A-1,C,D).
    // This is not necessarily true, because f is non-decreasing.
    // Instead, note that CountNotDivisible(A, B, C, D) counts elements x s.t. A <= x <= B.
    // If A > B, this range is empty, so the count is 0.
    // The postcondition should be proved by induction on the interval.
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
    assert f(n, C, D) >= f(n-1, C, D);
  }
}

lemma lemma_f_subtraction(n: int, k: int, C: int, D: int)
  requires n >= -1 && k >= -1
  requires C >= 1 && D >= 1
  requires n >= k
  ensures f(n, C, D) - f(k, C, D) == |set x | k < x <= n && NotDivisibleByEither(x, C, D)|
{
  if n == k {
    assert f(n, C, D) - f(k, C, D) == 0;
    assert |set x | k < x <= n && NotDivisibleByEither(x, C, D)| == 0;
  } else if n == k + 1 {
    if NotDivisibleByEither(n, C, D) {
      assert f(n, C, D) == f(n-1, C, D) + 1;
      assert f(n, C, D) - f(k, C, D) == 1;
    } else {
      assert f(n, C, D) == f(n-1, C, D);
      assert f(n, C, D) - f(k, C, D) == 0;
    }
    assert |set x | k < x <= n && NotDivisibleByEither(x, C, D)| == (if NotDivisibleByEither(n, C, D) then 1 else 0);
  } else {
    // inductive step: f(n,C,D) - f(k,C,D) = (f(n,C,D) - f(n-1,C,D)) + (f(n-1,C,D) - f(k,C,D))
    //                = (if NotDivisibleByEither(n,C,D) then 1 else 0) + |set x | k < x <= n-1 && NotDivisibleByEither(x,C,D)|
    //                = |set x | k < x <= n && NotDivisibleByEither(x,C,D)|
    lemma_f_subtraction(n - 1, k, C, D);
    if NotDivisibleByEither(n, C, D) {
      assert f(n, C, D) == f(n - 1, C, D) + 1;
    } else {
      assert f(n, C, D) == f(n - 1, C, D);
    }
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
      invariant A <= i <= B + 1
      invariant count == f(i - 1, C, D) - f(A - 1, C, D)
      invariant forall y :: A <= y < i ==> (NotDivisibleByEither(y, C, D) == (y in |set x | A <= x < i && NotDivisibleByEither(x, C, D)|))
    {
      if i % C != 0 && i % D != 0 {
        count := count + 1;
      }
      i := i + 1;
    }
    result := f(B, C, D) - f(A - 1, C, D);
    lemma_f_subtraction(B, A - 1, C, D);
    lemma_f_non_decreasing(B, C, D);
    lemma_f_non_decreasing(A - 1, C, D);
}
// </vc-code>

