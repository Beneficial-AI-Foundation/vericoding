predicate IsSorted(s:seq<int>)
{
 forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}


//ATOM

predicate SortSpec(input:seq<int>, output:seq<int>)
{
 && IsSorted(output)
 && multiset(output) == multiset(input)
}


//IMPL 

method fast_sort(input:seq<int>) returns (output:seq<int>)
ensures SortSpec(input, output)
{
    output := merge_sort(input);
}

method merge_sort(s: seq<int>) returns (result: seq<int>)
ensures IsSorted(result)
ensures multiset(result) == multiset(s)
{
    if |s| <= 1 {
        result := s;
    } else {
        var mid := |s| / 2;
        var left := s[..mid];
        var right := s[mid..];
        
        var sorted_left := merge_sort(left);
        var sorted_right := merge_sort(right);
        
        result := merge(sorted_left, sorted_right);
        
        /* code modified by LLM (iteration 1): Added lemma call to prove multiset equality */
        assert left + right == s;
        multiset_split_lemma(s, mid);
    }
}

/* code modified by LLM (iteration 1): Added helper lemma for multiset property */
lemma multiset_split_lemma(s: seq<int>, mid: int)
requires 0 <= mid <= |s|
ensures multiset(s[..mid]) + multiset(s[mid..]) == multiset(s)
{
    if |s| == 0 {
        return;
    }
    
    var left := s[..mid];
    var right := s[mid..];
    assert left + right == s;
    
    // Dafny should be able to prove this automatically with sequence properties
}

method merge(left: seq<int>, right: seq<int>) returns (result: seq<int>)
requires IsSorted(left)
requires IsSorted(right)
ensures IsSorted(result)
ensures multiset(result) == multiset(left) + multiset(right)
{
    result := [];
    var i, j := 0, 0;
    
    /* code modified by LLM (iteration 1): Fixed loop invariants and added sortedness maintenance */
    while i < |left| || j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant multiset(result) == multiset(left[..i]) + multiset(right[..j])
    invariant IsSorted(result)
    invariant |result| > 0 && i < |left| ==> result[|result|-1] <= left[i]
    invariant |result| > 0 && j < |right| ==> result[|result|-1] <= right[j]
    decreases |left| - i + |right| - j
    {
        if i == |left| {
            /* code modified by LLM (iteration 1): Added multiset assertion to maintain invariant */
            assert j < |right|;
            assert multiset(right[..j] + [right[j]]) == multiset(right[..j]) + multiset([right[j]]);
            assert right[..j+1] == right[..j] + [right[j]];
            if |result| > 0 {
                assert result[|result|-1] <= right[j];
            }
            result := result + [right[j]];
            j := j + 1;
        } else if j == |right| {
            /* code modified by LLM (iteration 1): Added multiset assertion to maintain invariant */
            assert i < |left|;
            assert multiset(left[..i] + [left[i]]) == multiset(left[..i]) + multiset([left[i]]);
            assert left[..i+1] == left[..i] + [left[i]];
            if |result| > 0 {
                assert result[|result|-1] <= left[i];
            }
            result := result + [left[i]];
            i := i + 1;
        } else if left[i] <= right[j] {
            /* code modified by LLM (iteration 1): Added multiset assertion to maintain invariant */
            assert multiset(left[..i] + [left[i]]) == multiset(left[..i]) + multiset([left[i]]);
            assert left[..i+1] == left[..i] + [left[i]];
            if |result| > 0 {
                assert result[|result|-1] <= left[i];
            }
            result := result + [left[i]];
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 1): Added multiset assertion to maintain invariant */
            assert right[j] < left[i];
            assert multiset(right[..j] + [right[j]]) == multiset(right[..j]) + multiset([right[j]]);
            assert right[..j+1] == right[..j] + [right[j]];
            if |result| > 0 {
                assert result[|result|-1] <= right[j];
            }
            result := result + [right[j]];
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Final assertion to complete the proof */
    assert i == |left| && j == |right|;
    assert multiset(result) == multiset(left[..|left|]) + multiset(right[..|right|]);
    assert left[..|left|] == left && right[..|right|] == right;
}