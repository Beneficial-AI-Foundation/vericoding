// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed precondition bounds to prevent underflow */
function HasDivisorInRange(n: int, start: int, current: int): bool
    requires n >= 2
    requires 2 <= start <= current
    decreases current - start
{
    if current < start then false
    else if IsDivisible(n, current) then true
    else if current > start then HasDivisorInRange(n, start, current - 1)
    else false
}

lemma HasDivisorInRangeCorrectness(n: int, start: int, current: int)
    requires n >= 2
    requires 2 <= start <= current
    ensures HasDivisorInRange(n, start, current) == (exists k :: start <= k <= current && IsDivisible(n, k))
    decreases current - start
{
    if current < start {
    } else if IsDivisible(n, current) {
    } else if current > start {
        HasDivisorInRangeCorrectness(n, start, current - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (exists k :: 2 <= k < n && IsDivisible(n, k))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): simplified implementation without helper functions */
{
    if n == 2 {
        result := false;
        return;
    }
    
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall k :: 2 <= k < i ==> !IsDivisible(n, k)
    {
        if IsDivisible(n, i) {
            result := true;
            return;
        }
        i := i + 1;
    }
    result := false;
}
// </vc-code>
