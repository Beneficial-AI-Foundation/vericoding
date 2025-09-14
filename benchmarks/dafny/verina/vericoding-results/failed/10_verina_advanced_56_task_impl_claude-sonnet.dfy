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
/* helper modified by LLM (iteration 5): fixed lemmas with proper induction and sequence reasoning */
lemma FilterNonZeroSubsequence(xs: seq<int>)
    ensures IsSubsequence(FilterNonZero(xs), xs)
    decreases |xs|
{
    if |xs| == 0 {
        // Base case: empty sequence
    } else {
        FilterNonZeroSubsequence(xs[1..]);
        if xs[0] != 0 {
            // xs[0] is included in FilterNonZero(xs)
            assert FilterNonZero(xs) == [xs[0]] + FilterNonZero(xs[1..]);
            // By induction hypothesis, IsSubsequence(FilterNonZero(xs[1..]), xs[1..])
            // Since xs[0] matches, we get IsSubsequence([xs[0]] + FilterNonZero(xs[1..]), xs)
        } else {
            // xs[0] is not included in FilterNonZero(xs)
            assert FilterNonZero(xs) == FilterNonZero(xs[1..]);
            // By induction hypothesis, IsSubsequence(FilterNonZero(xs[1..]), xs[1..])
            // This extends to IsSubsequence(FilterNonZero(xs), xs) by skipping xs[0]
        }
    }
}

lemma FilterNonZeroAppend(xs: seq<int>, x: int)
    ensures FilterNonZero(xs + [x]) == (if x != 0 then FilterNonZero(xs) + [x] else FilterNonZero(xs))
    decreases |xs|
{
    if |xs| == 0 {
        assert xs + [x] == [x];
        if x != 0 {
            assert FilterNonZero([x]) == [x];
            assert FilterNonZero(xs) + [x] == [] + [x] == [x];
        } else {
            assert FilterNonZero([x]) == [];
            assert FilterNonZero(xs) == [];
        }
    } else {
        FilterNonZeroAppend(xs[1..], x);
        if xs[0] != 0 {
            assert FilterNonZero(xs) == [xs[0]] + FilterNonZero(xs[1..]);
            assert FilterNonZero(xs + [x]) == [xs[0]] + FilterNonZero(xs[1..] + [x]);
            if x != 0 {
                assert FilterNonZero(xs[1..] + [x]) == FilterNonZero(xs[1..]) + [x];
                assert FilterNonZero(xs + [x]) == [xs[0]] + FilterNonZero(xs[1..]) + [x] == FilterNonZero(xs) + [x];
            } else {
                assert FilterNonZero(xs[1..] + [x]) == FilterNonZero(xs[1..]);
                assert FilterNonZero(xs + [x]) == [xs[0]] + FilterNonZero(xs[1..]) == FilterNonZero(xs);
            }
        } else {
            assert FilterNonZero(xs) == FilterNonZero(xs[1..]);
            assert FilterNonZero(xs + [x]) == FilterNonZero(xs[1..] + [x]);
        }
    }
}

lemma FilterNonZeroSlice(xs: seq<int>, i: int)
    requires 0 <= i <= |xs|
    ensures FilterNonZero(xs[0..i]) + FilterNonZero(xs[i..]) == FilterNonZero(xs)
    decreases i
{
    if i == 0 {
        assert xs[0..i] == [];
        assert xs[i..] == xs;
        assert FilterNonZero([]) == [];
        assert [] + FilterNonZero(xs) == FilterNonZero(xs);
    } else {
        FilterNonZeroSlice(xs, i-1);
        assert xs[0..i] == xs[0..i-1] + [xs[i-1]];
        FilterNonZeroAppend(xs[0..i-1], xs[i-1]);
        if xs[i-1] != 0 {
            assert FilterNonZero(xs[0..i]) == FilterNonZero(xs[0..i-1]) + [xs[i-1]];
            assert FilterNonZero(xs[0..i-1]) + FilterNonZero(xs[i-1..]) == FilterNonZero(xs);
            assert FilterNonZero(xs[i-1..]) == [xs[i-1]] + FilterNonZero(xs[i..]);
            assert FilterNonZero(xs[0..i]) + FilterNonZero(xs[i..]) == (FilterNonZero(xs[0..i-1]) + [xs[i-1]]) + FilterNonZero(xs[i..]);
            assert FilterNonZero(xs[0..i]) + FilterNonZero(xs[i..]) == FilterNonZero(xs[0..i-1]) + ([xs[i-1]] + FilterNonZero(xs[i..]));
            assert FilterNonZero(xs[0..i]) + FilterNonZero(xs[i..]) == FilterNonZero(xs[0..i-1]) + FilterNonZero(xs[i-1..]);
            assert FilterNonZero(xs[0..i]) + FilterNonZero(xs[i..]) == FilterNonZero(xs);
        } else {
            assert FilterNonZero(xs[0..i]) == FilterNonZero(xs[0..i-1]);
            assert FilterNonZero(xs[i-1..]) == FilterNonZero(xs[i..]);
            assert FilterNonZero(xs[0..i-1]) + FilterNonZero(xs[i-1..]) == FilterNonZero(xs);
            assert FilterNonZero(xs[0..i]) + FilterNonZero(xs[i..]) == FilterNonZero(xs[0..i-1]) + FilterNonZero(xs[i..]);
            assert FilterNonZero(xs[0..i]) + FilterNonZero(xs[i..]) == FilterNonZero(xs);
        }
    }
}

lemma CountValSlice(val: int, xs: seq<int>, i: int)
    requires 0 <= i <= |xs|
    ensures CountVal(val, xs[0..i]) + CountVal(val, xs[i..]) == CountVal(val, xs)
    decreases i
{
    if i == 0 {
        assert xs[0..i] == [];
        assert xs[i..] == xs;
        assert CountVal(val, []) == 0;
    } else {
        CountValSlice(val, xs, i-1);
        assert xs[0..i] == xs[0..i-1] + [xs[i-1]];
        assert xs[i-1..] == [xs[i-1]] + xs[i..];
        if xs[i-1] == val {
            assert CountVal(val, xs[0..i]) == CountVal(val, xs[0..i-1]) + 1;
            assert CountVal(val, xs[i-1..]) == 1 + CountVal(val, xs[i..]);
            assert CountVal(val, xs[0..i-1]) + CountVal(val, xs[i-1..]) == CountVal(val, xs);
            assert CountVal(val, xs[0..i]) + CountVal(val, xs[i..]) == (CountVal(val, xs[0..i-1]) + 1) + CountVal(val, xs[i..]);
            assert CountVal(val, xs[0..i]) + CountVal(val, xs[i..]) == CountVal(val, xs[0..i-1]) + (1 + CountVal(val, xs[i..]));
            assert CountVal(val, xs[0..i]) + CountVal(val, xs[i..]) == CountVal(val, xs[0..i-1]) + CountVal(val, xs[i-1..]);
        } else {
            assert CountVal(val, xs[0..i]) == CountVal(val, xs[0..i-1]);
            assert CountVal(val, xs[i-1..]) == CountVal(val, xs[i..]);
        }
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
    /* code modified by LLM (iteration 5): fixed invariants and added proper lemma applications */
    result := new int[xs.Length];
    var writePos := 0;
    
    // Initialize all positions to 0
    var k := 0;
    while k < xs.Length
        invariant 0 <= k <= xs.Length
        invariant forall j :: 0 <= j < k ==> result[j] == 0
    {
        result[k] := 0;
        k := k + 1;
    }
    
    // First pass: copy all non-zero elements
    var i := 0;
    writePos := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= writePos <= xs.Length
        invariant writePos == |FilterNonZero(xs[0..i])|
        invariant result[0..writePos] == FilterNonZero(xs[0..i])
        invariant forall j :: 0 <= j < writePos ==> result[j] != 0
        invariant forall j :: writePos <= j < xs.Length ==> result[j] == 0
    {
        if xs[i] != 0 {
            result[writePos] := xs[i];
            writePos := writePos + 1;
        }
        i := i + 1;
    }
    
    // Prove postconditions using helper lemmas
    FilterNonZeroSubsequence(xs[0..xs.Length]);
    assert IsSubsequence(FilterNonZero(xs[0..xs.Length]), xs[0..xs.Length]);
    assert result[0..writePos] == FilterNonZero(xs[0..xs.Length]);
    assert IsSubsequence(result[0..writePos], xs[0..xs.Length]);
    
    // Prove subsequence property for full result array
    assert forall j :: 0 <= j < writePos ==> result[j] != 0;
    assert forall j :: writePos <= j < xs.Length ==> result[j] == 0;
    assert result[0..result.Length] == result[0..writePos] + result[writePos..result.Length];
    
    // Count zeros correctly
    var numNonZeros := |FilterNonZero(xs[0..xs.Length])|;
    var numZeros := xs.Length - numNonZeros;
    assert writePos == numNonZeros;
    assert CountVal(0, result[0..writePos]) == 0;
    assert CountVal(0, result[writePos..result.Length]) == numZeros;
    CountValSlice(0, result[0..result.Length], writePos);
    assert CountVal(0, result[0..result.Length]) == CountVal(0, result[0..writePos]) + CountVal(0, result[writePos..result.Length]);
    assert CountVal(0, result[0..result.Length]) == 0 + numZeros == numZeros;
    
    // Prove original array has same number of zeros
    FilterNonZeroSlice(xs[0..xs.Length], numNonZeros);
    CountValSlice(0, xs[0..xs.Length], numNonZeros);
}
// </vc-code>
