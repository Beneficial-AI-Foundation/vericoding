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
/* code modified by LLM (iteration 5): Fixed loop invariant condition from xs.Length to result.Length, and improved the bounds for the loop invariant forall l :: k <= l < xs.Length ==> result[l] == 0 to forall l :: i <= l < xs.Length ==> result[l] == 0. */
{
    result := new int[xs.Length];
    var k := 0;

    for i := 0 to xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= k <= i
        invariant forall l :: 0 <= l < k ==> result[l] != 0
        invariant forall l :: k <= l < i ==> result[l] == 0
        invariant IsSubsequence(FilterNonZero(xs[0..i]), result[0..k])
        invariant CountVal(0, xs[0..i]) == CountVal(0, result[0..i])
        invariant forall l :: i <= l < result.Length ==> result[l] == 0
    {
        if i < xs.Length && xs[i] != 0 {
            result[k] := xs[i];
            k := k + 1;
        }
    }
}
// </vc-code>
