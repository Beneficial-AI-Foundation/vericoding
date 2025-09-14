// <vc-preamble>
predicate IsPrimePred(n: int)
{
    forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function IsPrime(n: int): bool
{
    n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

function FindLargestPrimeFactor(n: int, candidate: int): int
    requires 2 <= n <= 2147483646
    requires 1 <= candidate <= n
    decreases candidate
{
    if candidate == 1 then
        1
    else if n % candidate == 0 && IsPrime(candidate) then
        candidate
    else
        FindLargestPrimeFactor(n, candidate - 1)
}
// </vc-helpers>

// <vc-spec>
method LargestPrimeFactor(n: int) returns (result: int)
    requires 2 <= n <= 2147483646
    ensures 1 <= result <= n
    ensures result == 1 || (result > 1 && IsPrimePred(result))
// </vc-spec>
// <vc-code>
{
    var i := n;
    while i > 1
        invariant 1 <= i <= n
        invariant forall k :: i < k <= n && k > 1 && IsPrimePred(k) && n % k == 0 ==> false
        decreases i
    {
        if n % i == 0 {
            var isPrime := true;
            var j := 2;
            while j < i
                invariant 2 <= j <= i
                invariant isPrime == (forall k :: 2 <= k < j ==> i % k != 0)
                decreases i - j
            {
                if i % j == 0 {
                    isPrime := false;
                    break;
                }
                j := j + 1;
            }
            if isPrime {
                result := i;
                return;
            }
        }
        i := i - 1;
    }
    result := 1;
}
// </vc-code>
