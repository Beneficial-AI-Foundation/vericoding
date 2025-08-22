//IMPL 
method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..])) - multiset{val} * CountOccurrences(old(nums[..]), val)
{
    /* code modified by LLM (iteration 4): store original array content */
    ghost var originalNums := nums[..];
    
    newLength := 0;
    var i := 0;
    
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= newLength <= i
        invariant forall x :: x in nums[..newLength] ==> x != val
        /* code modified by LLM (iteration 4): maintain invariant about processed elements */
        invariant multiset(nums[..newLength]) == multiset(originalNums[..i]) - multiset{val} * CountOccurrences(originalNums[..i], val)
        /* code modified by LLM (iteration 4): unprocessed elements unchanged */
        invariant forall k :: i <= k < nums.Length ==> nums[k] == originalNums[k]
    {
        if nums[i] != val {
            nums[newLength] := nums[i];
            newLength := newLength + 1;
            
            /* code modified by LLM (iteration 4): assertions to help verification */
            assert nums[i] == originalNums[i];
            CountOccurrencesExtendLemma(originalNums[..i], originalNums[i], val);
            assert originalNums[..i+1] == originalNums[..i] + [originalNums[i]];
            assert CountOccurrences(originalNums[..i+1], val) == CountOccurrences(originalNums[..i], val);
            MultisetArithmeticLemma(originalNums[..i], originalNums[i], val);
        } else {
            /* code modified by LLM (iteration 4): handle val case */
            assert nums[i] == originalNums[i] == val;
            CountOccurrencesExtendLemma(originalNums[..i], originalNums[i], val);
            assert originalNums[..i+1] == originalNums[..i] + [originalNums[i]];
            assert CountOccurrences(originalNums[..i+1], val) == CountOccurrences(originalNums[..i], val) + 1;
            MultisetArithmeticLemma(originalNums[..i], originalNums[i], val);
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): final assertion */
    assert originalNums[..i] == originalNums;
}

/* code modified by LLM (iteration 4): helper function with decreases clause */
function CountOccurrences(s: seq<int>, val: int): nat
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == val then 1 else 0) + CountOccurrences(s[1..], val)
}

/* code modified by LLM (iteration 4): lemma for extending sequences */
lemma CountOccurrencesExtendLemma(s: seq<int>, elem: int, val: int)
    ensures CountOccurrences(s + [elem], val) == CountOccurrences(s, val) + (if elem == val then 1 else 0)
{
    if |s| == 0 {
        assert s + [elem] == [elem];
        assert CountOccurrences([elem], val) == (if elem == val then 1 else 0);
    } else {
        assert s + [elem] == [s[0]] + (s[1..] + [elem]);
        CountOccurrencesExtendLemma(s[1..], elem, val);
        assert CountOccurrences(s[1..] + [elem], val) == CountOccurrences(s[1..], val) + (if elem == val then 1 else 0);
    }
}

/* code modified by LLM (iteration 4): lemma for multiset arithmetic */
lemma MultisetArithmeticLemma(s: seq<int>, elem: int, val: int)
    ensures multiset(s + [elem]) == multiset(s) + multiset{elem}
    ensures if elem == val then
        multiset(s + [elem]) - multiset{val} * CountOccurrences(s + [elem], val) == 
        multiset(s) - multiset{val} * CountOccurrences(s, val)
    else
        multiset(s + [elem]) - multiset{val} * CountOccurrences(s + [elem], val) == 
        multiset(s) + multiset{elem} - multiset{val} * CountOccurrences(s, val)
{
    assert multiset(s + [elem]) == multiset(s) + multiset{elem};
    CountOccurrencesExtendLemma(s, elem, val);
    
    if elem == val {
        /* code modified by LLM (iteration 4): case when elem equals val */
        assert CountOccurrences(s + [elem], val) == CountOccurrences(s, val) + 1;
        assert multiset{val} * CountOccurrences(s + [elem], val) == 
               multiset{val} * CountOccurrences(s, val) + multiset{val};
        assert multiset(s + [elem]) == multiset(s) + multiset{val};
        assert multiset(s + [elem]) - multiset{val} * CountOccurrences(s + [elem], val) ==
               multiset(s) + multiset{val} - multiset{val} * CountOccurrences(s, val) - multiset{val};
        assert multiset(s) + multiset{val} - multiset{val} * CountOccurrences(s, val) - multiset{val} ==
               multiset(s) - multiset{val} * CountOccurrences(s, val);
    } else {
        /* code modified by LLM (iteration 4): case when elem doesn't equal val */
        assert CountOccurrences(s + [elem], val) == CountOccurrences(s, val);
        assert multiset{val} * CountOccurrences(s + [elem], val) == multiset{val} * CountOccurrences(s, val);
    }
}