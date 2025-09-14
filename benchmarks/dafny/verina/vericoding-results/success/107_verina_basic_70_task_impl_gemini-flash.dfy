// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LinearSearch3(a: seq<int>, p: int -> bool) returns (result: nat)
    requires 
        exists i :: 0 <= i < |a| && p(a[i])
    ensures 
        result < |a| &&
        p(a[result]) &&
        forall k :: 0 <= k < result ==> !p(a[k])
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |a| invariant 0 <= i <= |a| && forall k :: 0 <= k < i ==> !p(a[k])
    {
        if p(a[i]) {
            return i;
        }
        i := i + 1;
    }
    // This part should be unreachable due to the precondition
    // that such an element exists. In Dafny, this is usually handled
    // by a loop invariant or postcondition ensuring termination.
    // However, to satisfy the `returns (result: nat)` and `result < |a|`,
    // if the loop could theoretically fall through (which it shouldn't
    // given the precondition `exists i :: 0 <= i < |a| && p(a[i])`),
    // one might need to return a default or assert unreachable.
    // For this problem, the precondition guarantees the loop will find it.
    // We'll return i, which will be the first element satisfying p.
    // The `ensures` clause directly states properties of `result`.
    return i;
}
// </vc-code>
