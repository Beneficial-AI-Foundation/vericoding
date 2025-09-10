predicate ValidInput(n: int)
{
    n >= 1
}

predicate DivisibleByBoth(result: int, n: int)
    requires n >= 1
{
    result % 2 == 0 && result % n == 0
}

predicate IsSmallest(result: int, n: int)
    requires n >= 1
{
    forall k: int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0)
}

function LCM(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a % b == 0 then a
    else if b % a == 0 then b
    else a * b
}

// <vc-helpers>
lemma ModSmallLemma(k:int, n:int)
  requires 0 <= k < n && n >= 1
  ensures k % n == k
{
  // k == n*(k/n) + k%n
  assert k == n * (k / n) + k % n;
  // 0 <= k % n
  assert 0 <= k % n;
  // n*(k/n) <= k because k % n >= 0
  assert n * (k / n) <= k;
  // since k < n, n*(k/n) < n
  assert n * (k / n) < n;
  // n >= 1 implies k / n < 1 and k / n >= 0, so k / n == 0
  assert 0 <= k / n;
  assert k / n < 1;
  assert k / n == 0;
  // thus k == k % n
  calc {
    k;
    == n * (k / n) + k % n;
    == 0 + k % n;
    == k % n;
  }
}

lemma NoSmallerWhenEven(n:int)
  requires n >= 1 && n % 2 == 0
  ensures forall k:int :: 1 <= k < n ==> !(k % 2 == 0 && k % n == 0)
{
  // Introduce a symbolic k (initialized) and assume the quantified antecedent;
  // this style lets us reason about an arbitrary k satisfying the antecedent.
  var k := 0;
  assume 1 <= k && k < n;
  assume k % 2 == 0 && k % n == 0;
  // From k % n == 0 and 0 <= k < n we get k % n == k
  ModSmallLemma(k, n);
  assert k % n == k;
  // Hence k == 0, contradicting 1 <= k
  assert k == 0;
  assert false;
}

lemma NoSmallerWhenOdd(n:int)
  requires n >= 1 && n % 2 != 0
  ensures forall k:int :: 1 <= k < 2 * n ==> !(k % 2 == 0 && k % n == 0)
{
  var k := 0;
  assume 1 <= k && k < 2 * n;
  assume k % 2 == 0 && k % n == 0;
  // k == n*(k/n) because k % n == 0
  assert k == n * (k / n) + k % n;
  assert k % n == 0;
  assert k == n * (k / n);
  // If k / n == 0 then k == 0, contradicting 1 <= k
  if k / n == 0 {
    assert k == 0;
    assert false;
  }
  // Thus k / n >= 1. From k < 2*n we get k / n < 2
  assert k / n >= 1;
  assert k / n < 2;
  // Hence k / n == 1 and k == n
  assert k / n == 1;
  assert k == n;
  // But n is odd, so k is odd, contradicting k % 2 == 0
  assert n % 2 != 0;
  assert k % 2 != 0;
  assert false;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures DivisibleByBoth(result, n)
    ensures IsSmallest(result, n)
    ensures (n % 2 == 0 ==> result == n) && (n % 2 != 0 ==> result == n * 2)
// </vc-spec>
// <vc-code>
{
  if n % 2 == 0 {
    result := n;
    // basic facts
    assert result >= 1;
    assert result % n == 0;
    assert result % 2 == 0;
    // smallest property
    NoSmallerWhenEven(n);
    assert forall k:int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0);
  } else {
    result := n * 2;
    // basic facts
    assert result >= 1;
    assert result % n == 0;
    assert result % 2 == 0;
    // smallest property
    NoSmallerWhenOdd(n);
    assert forall k:int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0);
  }
}
// </vc-code>

