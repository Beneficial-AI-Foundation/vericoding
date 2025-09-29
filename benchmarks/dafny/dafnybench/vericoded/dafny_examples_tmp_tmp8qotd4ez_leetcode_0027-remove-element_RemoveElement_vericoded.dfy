

// <vc-helpers>
ghost function RemoveVal(s: multiset<int>, val: int): multiset<int>
{
    s[val := 0]
}

lemma MultisetRemoveValProperties(s: multiset<int>, val: int, x: int)
    ensures x != val ==> RemoveVal(s, val)[x] == s[x]
    ensures RemoveVal(s, val)[val] == 0
{
}

lemma RemoveValUnion(s1: multiset<int>, s2: multiset<int>, val: int)
    ensures RemoveVal(s1 + s2, val) == RemoveVal(s1, val) + RemoveVal(s2, val)
{
    // This follows from the definition of RemoveVal and multiset operations
}

lemma RemoveValSingleton(x: int, val: int)
    ensures x == val ==> RemoveVal(multiset{x}, val) == multiset{}
    ensures x != val ==> RemoveVal(multiset{x}, val) == multiset{x}
{
}
// </vc-helpers>

// <vc-spec>
method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
// </vc-spec>
// <vc-code>
{
    newLength := 0;
    var i := 0;
    
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= newLength <= i
        invariant forall j :: 0 <= j < newLength ==> nums[j] != val
        invariant multiset(nums[..newLength]) == RemoveVal(multiset(old(nums[..i])), val)
        invariant forall j :: newLength <= j < i ==> nums[j] == old(nums[j])
        invariant forall j :: i <= j < nums.Length ==> nums[j] == old(nums[j])
    {
        var currentVal := nums[i];
        assert currentVal == old(nums[i]) by {
            assert i <= i < nums.Length;
        }
        
        if currentVal != val {
            // Before assignment, prove the invariant will be maintained
            assert old(nums[..i+1]) == old(nums[..i]) + old([nums[i]]);
            assert multiset(old(nums[..i+1])) == multiset(old(nums[..i])) + multiset{old(nums[i])};
            
            nums[newLength] := currentVal;
            
            assert nums[..newLength+1] == nums[..newLength] + [nums[newLength]];
            assert multiset(nums[..newLength+1]) == multiset(nums[..newLength]) + multiset{nums[newLength]};
            assert nums[newLength] == currentVal;
            assert currentVal != val;
            assert old(nums[i]) != val;
            
            RemoveValSingleton(old(nums[i]), val);
            assert RemoveVal(multiset{old(nums[i])}, val) == multiset{old(nums[i])};
            
            RemoveValUnion(multiset(old(nums[..i])), multiset{old(nums[i])}, val);
            assert RemoveVal(multiset(old(nums[..i+1])), val) == RemoveVal(multiset(old(nums[..i])), val) + multiset{old(nums[i])};
            
            newLength := newLength + 1;
        } else {
            assert currentVal == val;
            assert old(nums[i]) == val;
            assert old(nums[..i+1]) == old(nums[..i]) + old([nums[i]]);
            assert multiset(old(nums[..i+1])) == multiset(old(nums[..i])) + multiset{old(nums[i])};
            
            RemoveValSingleton(old(nums[i]), val);
            assert RemoveVal(multiset{old(nums[i])}, val) == multiset{};
            
            RemoveValUnion(multiset(old(nums[..i])), multiset{old(nums[i])}, val);
            assert RemoveVal(multiset(old(nums[..i+1])), val) == RemoveVal(multiset(old(nums[..i])), val);
        }
        i := i + 1;
    }
    
    assert i == nums.Length;
    assert old(nums[..i]) == old(nums[..]);
    assert multiset(nums[..newLength]) == RemoveVal(multiset(old(nums[..])), val);
}
// </vc-code>

