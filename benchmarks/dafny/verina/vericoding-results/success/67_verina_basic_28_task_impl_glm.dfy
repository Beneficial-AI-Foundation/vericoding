// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add requires clause to prevent division by zero */
function IsDivisible(n: nat, d: nat): bool
    requires d != 0
{
    n % d == 0
}
// </vc-helpers>

// <vc-spec>
method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result ==> forall k: nat :: 2 <= k < n ==> n % k != 0
    ensures !result ==> exists k: nat :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implement prime number check with proper divisibility check */
{
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall k: nat :: 2 <= k < i ==> n % k != 0
    {
        if IsDivisible(n, i) {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
