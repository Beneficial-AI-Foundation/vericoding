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
        
        /* code modified by LLM (iteration 3): added lemma call to prove multiset equality */
        assert left + right == s;
        multiset_concat_lemma(left, right);
    }
}

/* code modified by LLM (iteration 3): added helper lemma for multiset concatenation */
lemma multiset_concat_lemma(a: seq<int>, b: seq<int>)
    ensures multiset(a + b) == multiset(a) + multiset(b)
{
}

method merge(left: seq<int>, right: seq<int>) returns (result: seq<int>)
    requires IsSorted(left)
    requires IsSorted(right)
    ensures IsSorted(result)
    ensures multiset(result) == multiset(left) + multiset(right)
{
    result := [];
    var i, j := 0, 0;
    
    while i < |left| || j < |right|
        invariant 0 <= i <= |left|
        invariant 0 <= j <= |right|
        invariant IsSorted(result)
        invariant multiset(result) == multiset(left[..i]) + multiset(right[..j])
        /* code modified by LLM (iteration 3): added ordering invariants between result and remaining elements */
        invariant |result| > 0 && i < |left| ==> result[|result|-1] <= left[i]
        invariant |result| > 0 && j < |right| ==> result[|result|-1] <= right[j]
        decreases |left| - i + |right| - j
    {
        if i == |left| {
            /* code modified by LLM (iteration 3): added assertion to help prove multiset invariant */
            assert right[..j+1] == right[..j] + [right[j]];
            result := result + [right[j]];
            j := j + 1;
        } else if j == |right| {
            /* code modified by LLM (iteration 3): added assertion to help prove multiset invariant */
            assert left[..i+1] == left[..i] + [left[i]];
            result := result + [left[i]];
            i := i + 1;
        } else if left[i] <= right[j] {
            /* code modified by LLM (iteration 3): added assertion to help prove multiset invariant */
            assert left[..i+1] == left[..i] + [left[i]];
            result := result + [left[i]];
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 3): added assertion to help prove multiset invariant */
            assert right[..j+1] == right[..j] + [right[j]];
            result := result + [right[j]];
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 3): added final assertions to help prove postconditions */
    assert i == |left| && j == |right|;
    assert left[..i] == left && right[..j] == right;
}