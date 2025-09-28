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
lemma CountAndFilter(s: seq<int>)
    ensures |FilterNonZero(s)| + CountVal(0, s) == |s|
    decreases |s|
{
    if |s| > 0 {
        CountAndFilter(s[1..]);
    }
}

lemma FilterNonZero_append(s1: seq<int>, s2: seq<int>)
    ensures FilterNonZero(s1 + s2) == FilterNonZero(s1) + FilterNonZero(s2)
    decreases |s1|
{
    if |s1| > 0 {
        FilterNonZero_append(s1[1..], s2);
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
    var L := xs.Length;
    result := new int[L];
    
    var num_zeros := CountVal(0, xs[0..L]);

    var i := 0;
    while i < num_zeros
        invariant 0 <= i <= num_zeros
        invariant forall k :: 0 <= k < i ==> result[k] == 0
    {
        result[i] := 0;
        i := i + 1;
    }

    var write_idx := num_zeros;
    var read_idx := 0;
    while read_idx < L
        invariant 0 <= read_idx <= L
        invariant num_zeros <= write_idx <= L
        invariant forall k :: 0 <= k < num_zeros ==> result[k] == 0
        invariant result[num_zeros..write_idx] == FilterNonZero(xs[0..read_idx])
    {
        FilterNonZero_append(xs[0..read_idx], [xs[read_idx]]);
        if xs[read_idx] != 0 {
            result[write_idx] := xs[read_idx];
            write_idx := write_idx + 1;
        }
        read_idx := read_idx + 1;
    }
    CountAndFilter(xs[0..L]);
}
// </vc-code>
