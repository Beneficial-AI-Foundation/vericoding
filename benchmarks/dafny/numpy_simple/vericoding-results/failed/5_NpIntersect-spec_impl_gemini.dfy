// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(arr: array<real>, x: real): bool
    reads arr
{
    exists i :: 0 <= i < arr.Length && arr[i] == x
}

/* helper modified by LLM (iteration 4): [changed from predicate to function to fix compilation error] */
function IsFirstOccurrence(a: array<real>, i: int): bool
    requires 0 <= i < a.Length
    reads a
{
    forall k :: 0 <= k < i ==> a[k] != a[i]
}

/* helper modified by LLM (iteration 5): [used alternative set comprehension syntax to fix parse error] */
function IntersectingIndicesSet(a: array<real>, b: array<real>, i: int): set<int>
    requires 0 <= i <= a.Length
    reads a, b
{
    {k | k: int, 0 <= k < i && IsFirstOccurrence(a, k) && Contains(b, a[k])}
}
// </vc-helpers>

// <vc-spec>
method Intersect(a: array<real>, b: array<real>) returns (result: array<real>)
    ensures
        result.Length < a.Length && result.Length < b.Length &&
        forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> (
            (a[i] == b[j] ==> exists k :: 0 <= k < result.Length && result[k] == a[i]) &&
            (a[i] != b[j] ==> !exists k :: 0 <= k < result.Length && result[k] == a[i])
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [no change, fix is in helpers] */
{
    // Pass 1: Count the number of unique elements in 'a' that are also in 'b'.
    var count := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant count == |IntersectingIndicesSet(a, b, i)|
    {
        if IsFirstOccurrence(a, i) && Contains(b, a[i]) {
            count := count + 1;
        }
        i := i + 1;
    }

    // Allocate the result array with the determined size.
    result := new real[count];

    // Pass 2: Populate the result array.
    var result_idx := 0;
    i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= result_idx <= count
        invariant result_idx == |IntersectingIndicesSet(a, b, i)|
        invariant forall k: int :: 0 <= k < result_idx ==> (exists l: int :: 0 <= l < i && IsFirstOccurrence(a, l) && Contains(b, a[l]) && result[k] == a[l])
        invariant forall k1: int, k2: int :: 0 <= k1 < k2 < result_idx ==> result[k1] != result[k2]
    {
        if IsFirstOccurrence(a, i) && Contains(b, a[i]) {
            assert result_idx < count;
            result[result_idx] := a[i];
            result_idx := result_idx + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
