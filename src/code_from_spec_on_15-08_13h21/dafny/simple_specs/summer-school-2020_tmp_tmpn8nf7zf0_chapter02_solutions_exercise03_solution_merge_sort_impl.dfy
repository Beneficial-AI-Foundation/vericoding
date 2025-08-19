predicate SortSpec(input: seq<int>, output: seq<int>)
{
    multiset(input) == multiset(output) && IsSorted(output)
}

predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma SequenceConcat(s:seq<int>, pivot:int)
 requires 0<=pivot<|s|
 ensures s[..pivot] + s[pivot..] == s
{
    // This is a built-in property of sequence slicing in Dafny
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
 ensures SortSpec(input, output)
{
    if |input| <= 1 {
        output := input;
    } else {
        var mid := |input| / 2;
        var left := merge_sort(input[..mid]);
        var right := merge_sort(input[mid..]);
        output := merge(left, right);
        
        // Prove the multiset property
        SequenceConcat(input, mid);
        MergePreservesMultiset(left, right, output);
        MultisetConcatProperty(input[..mid], input[mid..]);
    }
}

method merge(left: seq<int>, right: seq<int>) returns (result: seq<int>)
    requires IsSorted(left) && IsSorted(right)
    ensures IsSorted(result)
    ensures multiset(result) == multiset(left) + multiset(right)
{
    result := [];
    var i, j := 0, 0;
    
    /* code modified by LLM (iteration 2): Fixed loop invariant and added assertions to help prove multiset property */
    while i < |left| || j < |right|
        invariant 0 <= i <= |left| && 0 <= j <= |right|
        invariant IsSorted(result)
        invariant multiset(result) == multiset(left[..i]) + multiset(right[..j])
        invariant i < |left| ==> (|result| == 0 || result[|result|-1] <= left[i])
        invariant j < |right| ==> (|result| == 0 || result[|result|-1] <= right[j])
        decreases |left| - i + |right| - j
    {
        if i >= |left| {
            /* code modified by LLM (iteration 2): Added helper lemma call to prove multiset invariant */
            SliceExtensionLemma(right, j);
            result := result + [right[j]];
            j := j + 1;
        } else if j >= |right| {
            /* code modified by LLM (iteration 2): Added helper lemma call to prove multiset invariant */
            SliceExtensionLemma(left, i);
            result := result + [left[i]];
            i := i + 1;
        } else if left[i] <= right[j] {
            /* code modified by LLM (iteration 2): Added helper lemma call to prove multiset invariant */
            SliceExtensionLemma(left, i);
            result := result + [left[i]];
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 2): Added helper lemma call to prove multiset invariant */
            SliceExtensionLemma(right, j);
            result := result + [right[j]];
            j := j + 1;
        }
    }
    /* code modified by LLM (iteration 2): Added final assertions to prove postcondition */
    assert i == |left| && j == |right|;
    assert left[..i] == left && right[..j] == right;
    assert multiset(result) == multiset(left[..i]) + multiset(right[..j]);
}

/* code modified by LLM (iteration 3): Fixed type error by making lemma specific to int sequences */
lemma SliceExtensionLemma(s: seq<int>, k: int)
    requires 0 <= k < |s|
    ensures multiset(s[..k]) + multiset([s[k]]) == multiset(s[..k+1])
{
    assert s[..k+1] == s[..k] + [s[k]];
    MultisetConcatProperty(s[..k], [s[k]]);
}

lemma MergePreservesMultiset(left: seq<int>, right: seq<int>, merged: seq<int>)
    requires multiset(merged) == multiset(left) + multiset(right)
    ensures multiset(merged) == multiset(left + right)
{
    MultisetConcatProperty(left, right);
}

lemma MultisetConcatProperty(s1: seq<int>, s2: seq<int>)
    ensures multiset(s1 + s2) == multiset(s1) + multiset(s2)
{
    // This is a built-in property in Dafny
}