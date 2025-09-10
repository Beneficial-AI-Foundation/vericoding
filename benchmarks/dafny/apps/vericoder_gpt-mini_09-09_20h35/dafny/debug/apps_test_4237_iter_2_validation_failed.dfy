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
function f(x: int, C: int, D: int): int
  requires x >= 0 && C > 0 && D > 0
{
  |set n | 0 <= n <= x && NotDivisibleByEither(n, C, D)|
}

lemma CountEqualsF(A: int, B: int, C: int, D: int)
  requires ValidInput(A, B, C, D)
  ensures CountNotDivisible(A, B, C, D) == f(B, C, D) - f(A - 1, C, D)
{
  // Define the relevant sets
  var S1 := set x | A <= x <= B && NotDivisibleByEither(x, C, D);
  var S2 := set x | 0 <= x <= B && NotDivisibleByEither(x, C, D);
  var S3 := set x | 0 <= x <= A - 1 && NotDivisibleByEither(x, C, D);

  // Show S3 is subset of S2
  // From ValidInput we have A >= 1 and A <= B, so A - 1 <= B
  assert A >= 1;
  assert A <= B;
  assert A - 1 <= B;
  forall x :: (x in S3) ==> (x in S2)
  {
    assume x in S3;
    // x satisfies 0 <= x <= A-1 and NotDivisible...
    // since A-1 <= B, we get x <= B, so x in S2
    assert 0 <= x;
    assert x <= A - 1;
    assert x <= B;
    assert NotDivisibleByEither(x, C, D);
  }

  // Show S1 == S2 - S3
  forall x ::
    (x in S1) ==> (x in S2 - S3)
  {
    assume x in S1;
    // From x in S1, A <= x <= B and NotDivisible...
    assert A <= x;
    assert x <= B;
    assert NotDivisibleByEither(x, C, D);
    // Since A >= 1, 0 <= x holds
    assert 0 <= x;
    // x cannot be in S3 because x >= A > A-1
    assert !(x <= A - 1);
    // Thus x in S2 and not in S3
  }
  forall x ::
    (x in S2 - S3) ==> (x in S1)
  {
    assume x in S2 - S3;
    // x in S2 so 0 <= x <= B and NotDivisible...
    assert 0 <= x;
    assert x <= B;
    assert NotDivisibleByEither(x, C, D);
    // not in S3 means not (0 <= x <= A-1 and NotDivisible...), so not (x <= A-1)
    // hence x >= A
    assert !(x <= A - 1);
    assert x >= A;
    // Combined with x <= B gives A <= x <= B and NotDivisible...
    assert A <= x;
  }

  // Now relate cardinalities
  // CountNotDivisible(A,B,C,D) is |S1|
  assert CountNotDivisible(A, B, C, D) == |S1|;
  // Since S1 == S2 - S3:
  assert |S1| == |S2 - S3|;
  // Because S3 ⊆ S2, |S2 - S3| == |S2| - |S3|
  assert S3 <= S2;
  assert |S2 - S3| == |S2| - |S3|;
  // |S2| and |S3| match f(...)
  assert |S2| == f(B, C, D);
  assert |S3| == f(A - 1, C, D);

  // Chain equalities to conclude the lemma
  assert CountNotDivisible(A, B, C, D) == f(B, C, D) - f(A - 1, C, D);
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
  result := CountNotDivisible(A, B, C, D);
  CountEqualsF(A, B, C, D);
}
// </vc-code>

