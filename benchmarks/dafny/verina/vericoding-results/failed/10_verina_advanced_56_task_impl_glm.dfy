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
/* helper modified by LLM (iteration 2): added helper lemma for FilterNonZero properties */
lemma FilterNonZeroProperties(xs: seq<int>)
    ensures |FilterNonZero(xs)| == |xs| - CountVal(0, xs)
    ensures forall i :: 0 <= i < |FilterNonZero(xs)| ==> FilterNonZero(xs)[i] != 0
    ensures IsSubsequence(FilterNonZero(xs), xs)
{
    if |xs| == 0 {
    } else if xs[0] != 0 {
        FilterNonZeroProperties(xs[1..]);
    } else {
        FilterNonZeroProperties(xs[1..]);
    }
}
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
{
    /* code modified by LLM (iteration 2): fixed zero movement and subsequence preservation */
    result := new int[xs.Length];
    var nonZeroCount := 0;
    
    // First pass: copy non-zero elements in order
    for i := 0 to xs.Length
        invariant 0 <= nonZeroCount <= i <= xs.Length
        invariant nonZeroCount == |FilterNonZero(xs[0..i])|
        invariant forall k :: 0 <= k < nonZeroCount ==> result[k] != 0
        invariant IsSubsequence(FilterNonZero(xs[0..i]), result[0..nonZeroCount])
    {
        if xs[i] != 0 {
            result[nonZeroCount] := xs[i];
            nonZeroCount := nonZeroCount + 1;
        }
    }
    
    // Second pass: fill remaining positions with zeros
    var zeroCount := xs.Length - nonZeroCount;
    for j := nonZeroCount to xs.Length
        invariant nonZeroCount <= j <= xs.Length
        invariant j == nonZeroCount + (j - nonZeroCount)
        invariant forall k :: nonZeroCount <= k < j ==> result[k] == 0
        invariant CountVal(0, result[0..j]) == j - nonZeroCount
    {
        result[j] := 0;
    }
}
// </vc-code>
