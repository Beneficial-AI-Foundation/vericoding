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
/* helper modified by LLM (iteration 5): fixed subsequence proofs with proper subslice handling */
lemma FilterNonZeroPreservesOrder(xs: seq<int>, ys: seq<int>)
    requires IsSubsequence(xs, ys)
    ensures IsSubsequence(FilterNonZero(xs), FilterNonZero(ys))
    decreases |xs| + |ys|
{
    if |xs| == 0 {
        return;
    }
    if |ys| == 0 {
        assert |xs| > 0 && |ys| == 0;
        assert !IsSubsequence(xs, ys);
        assert false;
    }
    if xs[0] == ys[0] {
        FilterNonZeroPreservesOrder(xs[1..], ys[1..]);
        if xs[0] != 0 {
            assert FilterNonZero(xs) == [xs[0]] + FilterNonZero(xs[1..]);
            assert FilterNonZero(ys) == [ys[0]] + FilterNonZero(ys[1..]);
            assert FilterNonZero(xs)[0] == FilterNonZero(ys)[0];
            assert IsSubsequence(FilterNonZero(xs)[1..], FilterNonZero(ys)[1..]);
        } else {
            assert xs[0] == 0 && ys[0] == 0;
            assert FilterNonZero(xs) == FilterNonZero(xs[1..]);
            assert FilterNonZero(ys) == FilterNonZero(ys[1..]);
        }
    } else {
        FilterNonZeroPreservesOrder(xs, ys[1..]);
        if ys[0] != 0 {
            assert FilterNonZero(ys) == [ys[0]] + FilterNonZero(ys[1..]);
            assert IsSubsequence(FilterNonZero(xs), FilterNonZero(ys[1..]));            
        } else {
            assert FilterNonZero(ys) == FilterNonZero(ys[1..]);
        }
    }
}

/* helper modified by LLM (iteration 5): added stronger count preservation */
lemma CountValDistributive(val: int, xs: seq<int>, ys: seq<int>)
    ensures CountVal(val, xs + ys) == CountVal(val, xs) + CountVal(val, ys)
    decreases |xs|
{
    if |xs| == 0 {
        assert xs + ys == ys;
        assert CountVal(val, xs) == 0;
        return;
    }
    assert xs == [xs[0]] + xs[1..];
    assert xs + ys == [xs[0]] + (xs[1..] + ys);
    CountValDistributive(val, xs[1..], ys);
    if xs[0] == val {
        assert CountVal(val, xs + ys) == 1 + CountVal(val, xs[1..] + ys);
        assert CountVal(val, xs + ys) == 1 + CountVal(val, xs[1..]) + CountVal(val, ys);
        assert CountVal(val, xs) == 1 + CountVal(val, xs[1..]);
    } else {
        assert CountVal(val, xs + ys) == CountVal(val, xs[1..] + ys);
        assert CountVal(val, xs + ys) == CountVal(val, xs[1..]) + CountVal(val, ys);
        assert CountVal(val, xs) == CountVal(val, xs[1..]);
    }
}

lemma SubsequencePrefix(xs: seq<int>, ys: seq<int>)
    requires |xs| <= |ys|
    requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
    ensures IsSubsequence(xs, ys)
    decreases |xs|
{
    if |xs| == 0 {
        return;
    }
    assert xs[0] == ys[0];
    assert xs[1..] == ys[1..][0..|xs|-1];
    SubsequencePrefix(xs[1..], ys[1..]);
}

lemma SubsequenceAppend(xs: seq<int>, ys: seq<int>, zs: seq<int>)
    requires IsSubsequence(xs, ys)
    ensures IsSubsequence(xs, ys + zs)
    decreases |xs| + |ys|
{
    if |xs| == 0 {
        return;
    }
    if |ys| == 0 {
        assert false;
    }
    if xs[0] == ys[0] {
        SubsequenceAppend(xs[1..], ys[1..], zs);
        assert ys + zs == [ys[0]] + (ys[1..] + zs);
        assert IsSubsequence(xs[1..], ys[1..] + zs);
    } else {
        SubsequenceAppend(xs, ys[1..], zs);
        assert ys + zs == [ys[0]] + (ys[1..] + zs);
        assert IsSubsequence(xs, ys[1..] + zs);
    }
}

lemma FilterNonZeroCount(xs: seq<int>)
    ensures CountVal(0, FilterNonZero(xs)) == 0
    decreases |xs|
{
    if |xs| == 0 {
        return;
    }
    FilterNonZeroCount(xs[1..]);
    if xs[0] != 0 {
        assert FilterNonZero(xs) == [xs[0]] + FilterNonZero(xs[1..]);
        assert CountVal(0, FilterNonZero(xs)) == (if xs[0] == 0 then 1 else 0) + CountVal(0, FilterNonZero(xs[1..]));
        assert CountVal(0, FilterNonZero(xs)) == 0 + 0;
    } else {
        assert FilterNonZero(xs) == FilterNonZero(xs[1..]);
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
    /* code modified by LLM (iteration 5): fixed subsequence proof with proper array slicing */
    result := new int[xs.Length];
    var writePos := 0;
    
    // First pass: copy all non-zero elements
    for i := 0 to xs.Length
        invariant 0 <= writePos <= i
        invariant forall k :: 0 <= k < writePos ==> result[k] != 0
        invariant FilterNonZero(xs[0..i]) == result[0..writePos]
        invariant CountVal(0, xs[0..i]) + writePos == i
    {
        if xs[i] != 0 {
            result[writePos] := xs[i];
            writePos := writePos + 1;
        }
    }
    
    // Second pass: fill remaining positions with zeros
    for i := writePos to xs.Length
        invariant writePos <= i <= xs.Length
        invariant forall k :: writePos <= k < i ==> result[k] == 0
        invariant forall k :: 0 <= k < writePos ==> result[k] != 0
        invariant FilterNonZero(xs[0..xs.Length]) == result[0..writePos]
        invariant CountVal(0, xs[0..xs.Length]) + writePos == xs.Length
    {
        result[i] := 0;
    }
    
    // Prove subsequence property
    assert FilterNonZero(xs[0..xs.Length]) == result[0..writePos];
    
    // Use prefix subsequence lemma
    SubsequencePrefix(result[0..writePos], result[0..result.Length]);
    
    // Count properties
    FilterNonZeroCount(xs[0..xs.Length]);
    CountValDistributive(0, result[0..writePos], result[writePos..result.Length]);
    
    // Final verification
    assert forall k :: 0 <= k < writePos ==> result[k] != 0;
    assert forall k :: writePos <= k < result.Length ==> result[k] == 0;
    assert CountVal(0, result[0..writePos]) == 0;
    assert CountVal(0, result[writePos..result.Length]) == result.Length - writePos;
    assert CountVal(0, result[0..result.Length]) == result.Length - writePos;
    assert CountVal(0, xs[0..xs.Length]) == xs.Length - writePos;
}
// </vc-code>
