// <vc-preamble>
predicate IsOdd(n: int)
{
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> (forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrects loop bounds for empty array and ensures the postcondition. */
{
    var allOdd: bool := true;
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant allOdd == (forall k :: 0 <= k < i && k % 2 == 1 ==> IsOdd(a[k]))
    {
        if i < a.Length && i % 2 == 1 && !IsOdd(a[i]) {
            allOdd := false;
        }
    }
    result := allOdd;
}
// </vc-code>
