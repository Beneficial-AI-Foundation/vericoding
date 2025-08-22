//ATOM
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


//IMPL fast_sort
method fast_sort(input:seq<int>) returns (output:seq<int>)
ensures SortSpec(input, output)
{
    if |input| <= 1 {
        output := input;
        /* code modified by LLM (iteration 4): added assertion to help verify base case satisfies SortSpec */
        assert IsSorted(output);
        assert multiset(output) == multiset(input);
    } else {
        var mid := |input| / 2;
        var left := input[..mid];
        var right := input[mid..];
        
        var sorted_left := fast_sort(left);
        var sorted_right := fast_sort(right);
        
        /* code modified by LLM (iteration 4): added assertions to establish preconditions for merge */
        assert IsSorted(sorted_left);
        assert IsSorted(sorted_right);
        assert multiset(sorted_left) == multiset(left);
        assert multiset(sorted_right) == multiset(right);
        
        output := merge(sorted_left, sorted_right);
        
        /* code modified by LLM (iteration 4): added assertions to help verify SortSpec postcondition */
        assert IsSorted(output);
        assert multiset(output) == multiset(sorted_left) + multiset(sorted_right);
        MultisetSplitLemma(input, mid);
        assert multiset(left) + multiset(right) == multiset(input);
        assert multiset(output) == multiset(input);
    }
}

/* code modified by LLM (iteration 4): merge method with corrected implementation */
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
    invariant forall k :: 0 <= k < |result| ==> 
        (forall l :: i <= l < |left| ==> result[k] <= left[l]) &&
        (forall l :: j <= l < |right| ==> result[k] <= right[l])
    {
        if i >= |left| {
            /* code modified by LLM (iteration 4): simplified append operation */
            result := result + [right[j]];
            j := j + 1;
        } else if j >= |right| {
            /* code modified by LLM (iteration 4): simplified append operation */
            result := result + [left[i]];
            i := i + 1;
        } else if left[i] <= right[j] {
            /* code modified by LLM (iteration 4): simplified append operation */
            result := result + [left[i]];
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 4): simplified append operation */
            result := result + [right[j]];
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 4): final assertions to help verification */
    assert i == |left| && j == |right|;
    assert left[..i] == left;
    assert right[..j] == right;
}

/* code modified by LLM (iteration 4): added helper lemma for multiset split property */
lemma MultisetSplitLemma<T>(s: seq<T>, mid: int)
requires 0 <= mid <= |s|
ensures multiset(s[..mid]) + multiset(s[mid..]) == multiset(s)
{
    if mid == 0 {
        assert s[..mid] == [];
        assert s[mid..] == s;
    } else if mid == |s| {
        assert s[..mid] == s;
        assert s[mid..] == [];
    } else {
        assert s == s[..mid] + s[mid..];
    }
}