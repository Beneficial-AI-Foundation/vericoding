// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSorted(a: seq<int>) returns (result: bool)
    ensures
        result == (forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The loop invariant `0 <= i < |a|` was incorrect for the condition `i < |a| - 1`. Changed to `0 <= i <= |a| - 1` to match the loop termination condition and ensure correctness for both `i` and `i+1` accesses within the loop. The invariant `result == (forall k :: 0 <= k < i ==> a[k] <= a[k + 1])` remains important. Added a pre-condition check for empty sequences to simplify loop logic. */
{
    if |a| == 0 || |a| == 1 {
        result := true;
        return;
    }

    result := true;
    var i := 0;
    while i < |a| - 1
        invariant 0 <= i <= |a| - 1
        invariant result == (forall k :: 0 <= k < i ==> a[k] <= a[k + 1])
    {
        if a[i] > a[i+1]
        {
            result := false;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
