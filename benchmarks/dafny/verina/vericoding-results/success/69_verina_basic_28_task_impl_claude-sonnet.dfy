// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isDivisor(n: nat, k: nat): bool
    requires k > 0
{
    n % k == 0
}

function hasDivisorInRange(n: nat, start: nat, end: nat): bool
    requires start <= end
    requires start > 0 || start == 0
    decreases end - start
{
    if start >= end then false
    else if start > 0 && n % start == 0 then true
    else hasDivisorInRange(n, start + 1, end)
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
    /* code modified by LLM (iteration 2): fixed division by zero by adding guards */
    var k := 2;
    while k < n
        invariant 2 <= k <= n
        invariant forall j: nat :: 2 <= j < k ==> n % j != 0
    {
        if n % k == 0 {
            result := false;
            return;
        }
        k := k + 1;
    }
    result := true;
}
// </vc-code>
