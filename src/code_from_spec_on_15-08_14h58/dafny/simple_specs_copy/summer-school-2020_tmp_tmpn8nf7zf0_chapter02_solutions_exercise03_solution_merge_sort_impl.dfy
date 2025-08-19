// IMPL
lemma SequenceConcat(s:seq<int>, pivot:int)
 requires 0<=pivot<|s|
 ensures s[..pivot] + s[pivot..] == s
{
}

predicate SortSpec(input: seq<int>, output: seq<int>)
{
    multiset(input) == multiset(output) && Sorted(output)
}

predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method merge(left: seq<int>, right: seq<int>) returns (result: seq<int>)
    requires Sorted(left) && Sorted(right)
    ensures Sorted(result)
    ensures multiset(result) == multiset(left) + multiset(right)
{
    result := [];
    var i, j := 0, 0;
    
    /* code modified by LLM (iteration 1): Fixed invariants and added helper lemmas */
    while i < |left| || j < |right|
        invariant 0 <= i <= |left| && 0 <= j <= |right|
        invariant Sorted(result)
        invariant multiset(result) == multiset(left[..i]) + multiset(right[..j])
        invariant forall k :: 0 <= k < |result| ==> 
            (i < |left| ==> result[k] <= left[i]) &&
            (j < |right| ==> result[k] <= right[j])
        decreases |left| - i + |right| - j
    {
        if i >= |left| {
            /* code modified by LLM (iteration 1): Added assertions to help prove invariants */
            assert j < |right|;
            assert right[..j] + [right[j]] == right[..j+1];
            result := result + [right[j]];
            j := j + 1;
        } else if j >= |right| {
            /* code modified by LLM (iteration 1): Added assertions to help prove invariants */
            assert i < |left|;
            assert left[..i] + [left[i]] == left[..i+1];
            result := result + [left[i]];
            i := i + 1;
        } else if left[i] <= right[j] {
            /* code modified by LLM (iteration 1): Added assertions to help prove invariants */
            assert left[..i] + [left[i]] == left[..i+1];
            result := result + [left[i]];
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 1): Added assertions to help prove invariants */
            assert right[..j] + [right[j]] == right[..j+1];
            result := result + [right[j]];
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Added final assertions to prove postconditions */
    assert i == |left| && j == |right|;
    assert left[..i] == left && right[..j] == right;
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
 ensures SortSpec(input, output)
{
    if |input| <= 1 {
        output := input;
        return;
    }
    
    var mid := |input| / 2;
    var left := merge_sort(input[..mid]);
    var right := merge_sort(input[mid..]);
    
    SequenceConcat(input, mid);
    
    output := merge(left, right);
}