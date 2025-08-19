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
/* code modified by LLM (iteration 4): Fixed decreases clause position */
decreases |input|
{
    /* code modified by LLM (iteration 4): Complete quicksort implementation with proper termination */
    if |input| <= 1 {
        output := input;
        return;
    }
    
    var pivot := input[0];
    var less := [];
    var equal := [];
    var greater := [];
    
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant forall x :: x in less ==> x < pivot
        invariant forall x :: x in equal ==> x == pivot
        invariant forall x :: x in greater ==> x > pivot
        invariant multiset(less) + multiset(equal) + multiset(greater) == multiset(input[..i])
    {
        if input[i] < pivot {
            less := less + [input[i]];
        } else if input[i] == pivot {
            equal := equal + [input[i]];
        } else {
            greater := greater + [input[i]];
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added assertion to establish partition properties */
    assert multiset(less) + multiset(equal) + multiset(greater) == multiset(input);
    assert |equal| >= 1; // pivot is in equal
    assert |less| < |input|;
    assert |greater| < |input|;
    
    var sorted_less := fast_sort(less);
    var sorted_greater := fast_sort(greater);
    
    output := sorted_less + equal + sorted_greater;
    
    /* code modified by LLM (iteration 4): Added verification assertions for multiset preservation */
    assert multiset(output) == multiset(sorted_less) + multiset(equal) + multiset(greater);
    assert multiset(output) == multiset(less) + multiset(equal) + multiset(greater);
    assert multiset(output) == multiset(input);
    
    /* code modified by LLM (iteration 4): Added assertions for sorting properties */
    assert IsSorted(sorted_less);
    assert IsSorted(sorted_greater);
    assert forall x :: x in sorted_less ==> x < pivot;
    assert forall x :: x in equal ==> x == pivot;
    assert forall x :: x in sorted_greater ==> x > pivot;
    
    /* code modified by LLM (iteration 4): Added lemma call to prove concatenation preserves sorting */
    ConcatenationPreservesSorting(sorted_less, equal, sorted_greater, pivot);
    assert IsSorted(output);
}

/* code modified by LLM (iteration 4): Improved helper lemma for concatenation sorting property */
lemma ConcatenationPreservesSorting(left: seq<int>, middle: seq<int>, right: seq<int>, pivot: int)
    requires IsSorted(left)
    requires IsSorted(middle)
    requires IsSorted(right)
    requires forall x :: x in left ==> x < pivot
    requires forall x :: x in middle ==> x == pivot
    requires forall x :: x in right ==> x > pivot
    ensures IsSorted(left + middle + right)
{
    var result := left + middle + right;
    
    /* code modified by LLM (iteration 4): Simplified proof structure with better case handling */
    if |result| <= 1 {
        return;
    }
    
    forall i | 0 <= i < |result| - 1
        ensures result[i] <= result[i + 1]
    {
        if i < |left| - 1 {
            // Both elements in left part
            assert result[i] == left[i];
            assert result[i + 1] == left[i + 1];
        } else if i == |left| - 1 && |left| > 0 {
            // Transition from left to middle/right
            assert result[i] == left[i];
            assert left[i] < pivot;
            if |middle| > 0 {
                assert result[i + 1] == middle[0] == pivot;
            } else {
                assert result[i + 1] == right[0];
                assert right[0] > pivot;
            }
        } else if |left| <= i < |left| + |middle| - 1 {
            // Both elements in middle part
            var j := i - |left|;
            assert result[i] == middle[j] == pivot;
            assert result[i + 1] == middle[j + 1] == pivot;
        } else if i == |left| + |middle| - 1 && |middle| > 0 && |right| > 0 {
            // Transition from middle to right
            assert result[i] == middle[|middle| - 1] == pivot;
            assert result[i + 1] == right[0];
            assert right[0] > pivot;
        } else {
            // Both elements in right part
            var j := i - |left| - |middle|;
            assert 0 <= j < |right| - 1;
            assert result[i] == right[j];
            assert result[i + 1] == right[j + 1];
        }
    }
}