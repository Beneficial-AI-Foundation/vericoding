// <vc-preamble>
/* Count how many times a specific value appears in the sequence */
function CountVal(val: int, xs: seq<int>): nat 
    decreases |xs|
{
    if |xs| == 0 then
        0
    else
        var rest := CountVal(val, xs[1..]);
        if xs[0] == val then rest + 1 else rest
}

/* Check whether one sequence is a subsequence of another (preserving relative order) */
predicate IsSubsequence(xs: seq<int>, ys: seq<int>) 
    decreases |xs| + |ys|
{
    if |xs| == 0 then
        true
    else if |ys| == 0 then
        false
    else
        if xs[0] == ys[0] then
            IsSubsequence(xs[1..], ys[1..])
        else
            IsSubsequence(xs, ys[1..])
}

function FilterNonZero(xs: seq<int>): seq<int>
{
    if |xs| == 0 then []
    else if xs[0] != 0 then [xs[0]] + FilterNonZero(xs[1..])
    else FilterNonZero(xs[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed TotalZeroes since it's just a wrapper around CountVal */
// </vc-helpers>

// <vc-spec>
method MoveZeroes(xs: array<int>) returns (result: array<int>)
    ensures
        /* All non-zero elements must maintain their relative order */
        IsSubsequence(FilterNonZero(xs[0..xs.Length]), result[0..result.Length])
        /* All zeroes must be located at the end of the output array */
        && (forall i :: 0 <= i < result.Length && result[i] != 0 ==> 
            forall j :: i < j < result.Length ==> result[j] != 0)
        /* The output must contain the same number of elements */
        && xs.Length == result.Length
        /* The number of zeroes must remain unchanged */
        && CountVal(0, xs[0..xs.Length]) == CountVal(0, result[0..result.Length])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adjusted invariants and loop logic for correctness */
{
    var write_idx := 0;
    result := new int[xs.Length];

    for i := 0 to xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= write_idx <= i
        invariant FilterNonZero(xs[0..i]) == result[0..write_idx]
        invariant forall k :: 0 <= k < write_idx ==> result[k] != 0
        invariant forall k :: write_idx <= k < i ==> result[k] == 0
        invariant CountVal(0, xs[0..i]) == CountVal(0, result[0..i])
        invariant (forall k :: i <= k < xs.Length ==> result[k] == 0)
    {
        if i < xs.Length && xs[i] != 0 {
            result[write_idx] := xs[i];
            write_idx := write_idx + 1;
        } else if i < xs.Length && xs[i] == 0 {
            // This element is a zero, it will be placed at the end later
        }
    }

    // Fill the remaining spots with zeroes
    while write_idx < xs.Length
        invariant 0 <= write_idx <= xs.Length
        invariant forall k :: 0 <= k < write_idx ==> result[k] != 0
        invariant forall k :: write_idx <= k < xs.Length ==> result[k] == 0
        invariant CountVal(0, xs[0..xs.Length]) == CountVal(0, result[0..write_idx]) + (xs.Length - write_idx)
    {
        result[write_idx] := 0;
        write_idx := write_idx + 1;
    }
}
// </vc-code>
