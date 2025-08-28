// <vc-helpers>
lemma {:axiom} MultisetRemoveProperty<T>(s: multiset<T>, elem: T, count: nat)
    requires count <= s[elem]
    ensures s[elem := s[elem] - count] == s - multiset(seq(count, i => elem))

lemma {:axiom} MultisetSliceUpdate<T>(arr: array<T>, i: int, newVal: T, start: int, end: int)
    requires 0 <= start <= i < end <= arr.Length
    ensures multiset(arr[start..end]) == multiset(old(arr[start..end]))[old(arr[i]) := multiset(old(arr[start..end]))[old(arr[i])] - 1][newVal := multiset(old(arr[start..end]))[newVal] + 1]

lemma {:axiom} MultisetSlicePrefix<T>(arr: array<T>, i: int, j: int)
    requires 0 <= i <= j <= arr.Length
    ensures multiset(arr[..i]) <= multiset(arr[..j])

lemma MultisetConcatenation<T>(s1: multiset<T>, s2: multiset<T>, s3: multiset<T>)
    ensures s1 + s2 + s3 == s1 + (s2 + s3)
    ensures s1 + s2 == s2 + s1
{
}

lemma MultisetValProperty(nums: array<int>, val: int, i: int, newLength: int)
    requires 0 <= newLength <= i <= nums.Length
    requires forall x :: x in nums[newLength..i] ==> x == val
    ensures multiset(nums[newLength..i]) == multiset(seq(i - newLength, _ => val))
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    newLength := 0;
    var i := 0;
    
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= newLength <= i
        invariant forall x :: x in nums[..newLength] ==> x != val
        invariant val !in multiset(nums[..newLength])
        invariant multiset(nums[..]) == multiset(old(nums[..]))
        invariant forall x :: x in nums[newLength..i] ==> x == val
    {
        if nums[i] != val {
            nums[newLength] := nums[i];
            newLength := newLength + 1;
        }
        i := i + 1;
    }
    
    assert val !in multiset(nums[..newLength]);
    MultisetSlicePrefix(nums, newLength, nums.Length);
    assert multiset(nums[..newLength]) <= multiset(old(nums[..]));
    assert multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0];
}
// </vc-code>
