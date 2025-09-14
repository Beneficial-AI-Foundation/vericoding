// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LastPosition(a: array<int>, elem: int) returns (result: int)
    requires 0 < a.Length < 100_000
    requires exists i :: 0 <= i < a.Length && a[i] == elem
    ensures 0 <= result < a.Length
    ensures forall i :: result < i < a.Length ==> a[i] != elem
    ensures a[result] == elem
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to fix termination */
    result := 0;
    
    // Find the first occurrence to initialize result properly
    var i := 0;
    while a[i] != elem
        invariant 0 <= i < a.Length
        invariant forall j :: 0 <= j < i ==> a[j] != elem
        decreases a.Length - i
    {
        i := i + 1;
    }
    result := i;
    
    // Now find the last occurrence
    i := i + 1;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= result < a.Length
        invariant a[result] == elem
        invariant forall j :: result < j < i ==> a[j] != elem
    {
        if a[i] == elem {
            result := i;
        }
        i := i + 1;
    }
}
// </vc-code>
