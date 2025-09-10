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
lemma LCMLemma(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures LCM(a, b) % a == 0 && LCM(a, b) % b == 0
{
}

lemma IsSmallestLemma(result: int, n: int)
  requires n >= 1 && result % 2 == 0 && result % n == 0
  requires result == (if n % 2 == 0 then n else n * 2)
  ensures IsSmallest(result, n)
{
  assert forall k: int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0) by {
    forall k: int | 1 <= k < result 
      ensures !(k % 2 == 0 && k % n == 0)
    {
      if n % 2 == 0 {
        // n is even, result = n, which is the smallest even number
        if k % 2 == 0 {
          assert k < n;
          // Since k is even and < n, it can't be divisible by n (unless n > k)
          assert k % n == k != 0;
        }
      } else {
        // n is odd, result = 2n
        if k % 2 == 0 && k % n == 0 {
          // k is a common multiple, so k = m * n where m >= 1
          // Since k is even, and n is odd, m must be even
          var m := k / n;
          assert k == m * n;
          assert m >= 2;  // m must be at least 2 to make k even
          assert k >= 2 * n;
          assert result == 2 * n <= k;
          assert k < result ==> false;
        }
      }
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
    result := n * 2;
  }
}
// </vc-code>

