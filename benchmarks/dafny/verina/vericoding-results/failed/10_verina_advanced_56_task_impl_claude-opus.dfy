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
/* helper modified by LLM (iteration 5): Fixed SubsequenceSkip and added FilterNonZero lemmas */
lemma FilterNonZeroPreservesCount(xs: seq<int>, val: int)
    requires val != 0
    ensures CountVal(val, xs) == CountVal(val, FilterNonZero(xs))
    decreases |xs|
{
    if |xs| == 0 {
    } else if xs[0] != 0 {
        FilterNonZeroPreservesCount(xs[1..], val);
    } else {
        FilterNonZeroPreservesCount(xs[1..], val);
    }
}

lemma SubsequenceSkip(xs: seq<int>, ys: seq<int>)
    requires |ys| > 0
    requires IsSubsequence(xs, ys[1..])
    ensures IsSubsequence(xs, ys)
    decreases |xs|
{
    if |xs| == 0 {
    } else if xs[0] == ys[0] {
        SubsequenceSkip(xs[1..], ys[1..]);
    } else {
        // xs is a subsequence of ys[1..], so it's also a subsequence of ys
    }
}

lemma SubsequenceTransitive(xs: seq<int>, ys: seq<int>, zs: seq<int>)
    requires IsSubsequence(xs, ys)
    requires IsSubsequence(ys, zs)
    ensures IsSubsequence(xs, zs)
    decreases |xs|, |ys|, |zs|
{
    if |xs| == 0 {
    } else if |ys| == 0 {
        assert false;
    } else if |zs| == 0 {
        assert false;
    } else {
        if xs[0] == ys[0] {
            if ys[0] == zs[0] {
                SubsequenceTransitive(xs[1..], ys[1..], zs[1..]);
            } else {
                assert IsSubsequence(ys, zs[1..]);
                SubsequenceTransitive(xs, ys, zs[1..]);
            }
        } else {
            assert IsSubsequence(xs, ys[1..]);
            if ys[0] == zs[0] {
                SubsequenceTransitive(xs, ys[1..], zs[1..]);
            } else {
                assert IsSubsequence(ys, zs[1..]);
                if |ys| > 1 {
                    assert IsSubsequence(ys[1..], zs[1..]) || IsSubsequence(ys[1..], zs);
                    if IsSubsequence(ys[1..], zs[1..]) {
                        SubsequenceTransitive(xs, ys[1..], zs[1..]);
                    } else {
                        SubsequenceTransitive(xs, ys[1..], zs);
                    }
                } else {
                    assert |ys| == 1;
                    assert IsSubsequence([], zs[1..]);
                    assert IsSubsequence(xs, []);
                    assert false;
                }
            }
        }
    }
}

lemma SubsequenceRefl(xs: seq<int>)
    ensures IsSubsequence(xs, xs)
    decreases |xs|
{
    if |xs| == 0 {
    } else {
        SubsequenceRefl(xs[1..]);
    }
}

lemma SubsequencePrefix(xs: seq<int>, ys: seq<int>)
    requires |xs| <= |ys|
    requires xs == ys[0..|xs|]
    ensures IsSubsequence(xs, ys)
    decreases |xs|
{
    if |xs| == 0 {
    } else {
        assert xs[0] == ys[0];
        SubsequencePrefix(xs[1..], ys[1..]);
    }
}

lemma CountValSplit(val: int, xs: seq<int>, n: int)
    requires 0 <= n <= |xs|
    ensures CountVal(val, xs) == CountVal(val, xs[0..n]) + CountVal(val, xs[n..])
    decreases n
{
    if n == 0 {
        assert xs[0..n] == [];
        assert xs[n..] == xs;
    } else if n == |xs| {
        assert xs[0..n] == xs;
        assert xs[n..] == [];
    } else {
        CountValSplit(val, xs[1..], n-1);
        assert xs[1..][0..n-1] == xs[1..n];
        assert xs[1..][n-1..] == xs[n..];
    }
}

lemma FilterNonZeroCorrect(xs: seq<int>, i: int)
    requires 0 <= i <= |xs|
    ensures |FilterNonZero(xs[0..i])| <= i
    ensures forall k :: 0 <= k < |FilterNonZero(xs[0..i])| ==> FilterNonZero(xs[0..i])[k] != 0
    decreases i
{
    if i == 0 {
        assert xs[0..i] == [];
    } else {
        FilterNonZeroCorrect(xs, i-1);
        assert xs[0..i] == xs[0..i-1] + [xs[i-1]];
        if xs[i-1] != 0 {
            assert FilterNonZero(xs[0..i]) == FilterNonZero(xs[0..i-1]) + [xs[i-1]];
        } else {
            assert FilterNonZero(xs[0..i]) == FilterNonZero(xs[0..i-1]);
        }
    }
}

lemma FilterNonZeroStep(xs: seq<int>, i: int)
    requires 0 <= i < |xs|
    ensures FilterNonZero(xs[0..i+1]) == if xs[i] != 0 then FilterNonZero(xs[0..i]) + [xs[i]] else FilterNonZero(xs[0..i])
{
    assert xs[0..i+1] == xs[0..i] + [xs[i]];
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
/* code modified by LLM (iteration 5): Fixed verification issues and corrected assertions */
{
    result := new int[xs.Length];
    var nonZeroIndex := 0;
    var nonZeroSeq := [];
    
    for i := 0 to xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= nonZeroIndex <= i
        invariant forall k :: 0 <= k < nonZeroIndex ==> result[k] != 0
        invariant nonZeroSeq == FilterNonZero(xs[0..i])
        invariant |nonZeroSeq| == nonZeroIndex
        invariant forall k :: 0 <= k < nonZeroIndex ==> result[k] == nonZeroSeq[k]
    {
        if xs[i] != 0 {
            result[nonZeroIndex] := xs[i];
            nonZeroSeq := nonZeroSeq + [xs[i]];
            nonZeroIndex := nonZeroIndex + 1;
        }
        FilterNonZeroStep(xs, i);
    }
    
    assert nonZeroSeq == FilterNonZero(xs[0..xs.Length]);
    
    var zeroCount := CountVal(0, xs[0..xs.Length]);
    var zerosAdded := 0;
    for i := nonZeroIndex to xs.Length
        invariant nonZeroIndex <= i <= xs.Length
        invariant forall k :: 0 <= k < nonZeroIndex ==> result[k] != 0
        invariant forall k :: nonZeroIndex <= k < i ==> result[k] == 0
        invariant zerosAdded == i - nonZeroIndex
        invariant zerosAdded <= xs.Length - nonZeroIndex
    {
        result[i] := 0;
        zerosAdded := zerosAdded + 1;
    }
    
    // Prove subsequence property
    assert forall k :: 0 <= k < |FilterNonZero(xs[0..xs.Length])| ==> result[k] == FilterNonZero(xs[0..xs.Length])[k];
    SubsequenceRefl(FilterNonZero(xs[0..xs.Length]));
    SubsequencePrefix(FilterNonZero(xs[0..xs.Length]), result[0..result.Length]);
    
    // Prove count property
    CountValSplit(0, result[0..result.Length], nonZeroIndex);
    FilterNonZeroCorrect(xs[0..xs.Length], xs.Length);
    assert forall k :: 0 <= k < |FilterNonZero(xs[0..xs.Length])| ==> FilterNonZero(xs[0..xs.Length])[k] != 0;
    
    // Count zeros in result prefix is 0
    var j := 0;
    while j < nonZeroIndex
        invariant 0 <= j <= nonZeroIndex
        invariant CountVal(0, result[0..j]) == 0
    {
        assert result[j] != 0;
        j := j + 1;
    }
    
    assert CountVal(0, result[nonZeroIndex..result.Length]) == result.Length - nonZeroIndex;
}
// </vc-code>
