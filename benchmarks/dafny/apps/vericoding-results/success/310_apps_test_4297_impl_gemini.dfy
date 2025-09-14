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
lemma IsSmallestForOddN(n: int)
    requires n >= 1 && n % 2 != 0
    ensures IsSmallest(n * 2, n)
{
    forall k: int
        | 1 <= k < n * 2
        ensures !(k % 2 == 0 && k % n == 0)
    {
        if k % 2 == 0 && k % n == 0 {
            var q := k / n;
            assert k == q * n;

            assert q >= 1;

            assert q*n < 2*n;
            assert q < 2;

            assert q == 1;
            assert k == n;

            assert n % 2 == 0;
            assert false;
        }
    }
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
  } else {
    result := 2 * n;
    IsSmallestForOddN(n);
  }
}
// </vc-code>

