// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate NoDivisorsUpTo(n: nat, limit: nat)
{
  forall k: nat :: 2 <= k < limit ==> n % k != 0
}
// </vc-helpers>

// <vc-spec>
method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result ==> forall k: nat :: 2 <= k < n ==> n % k != 0
    ensures !result ==> exists k: nat :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant NoDivisorsUpTo(n, i)
    {
        if n % i == 0 {
            result := false;
            return;
        }
        i := i + 1;
    }
    result := true;
}
// </vc-code>
