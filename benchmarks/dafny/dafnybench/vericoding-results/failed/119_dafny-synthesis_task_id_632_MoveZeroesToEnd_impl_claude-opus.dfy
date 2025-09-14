method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
  assume{:axiom} false;
}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}

// <vc-helpers>
lemma CountPermutation(s1: seq<int>, s2: seq<int>, value: int)
    requires multiset(s1) == multiset(s2)
    ensures count(s1, value) == count(s2, value)
    decreases |s1|
{
    if |s1| == 0 {
        assert |s2| == 0;
    } else {
        assert s1[0] in multiset(s1);
        assert s1[0] in multiset(s2);
        var i :| 0 <= i < |s2| && s2[i] == s1[0];
        var s2' := s2[..i] + s2[i+1..];
        
        assert |s2'| == |s2| - 1;
        assert s2 == s2[..i] + [s2[i]] + s2[i+1..];
        assert multiset(s2) == multiset(s2[..i]) + multiset([s2[i]]) + multiset(s2[i+1..]);
        assert multiset(s2') == multiset(s2[..i]) + multiset(s2[i+1..]);
        assert multiset(s2) == multiset([s2[i]]) + multiset(s2');
        
        assert s1 == [s1[0]] + s1[1..];
        assert multiset(s1) == multiset([s1[0]]) + multiset(s1[1..]);
        assert multiset([s1[0]]) == multiset([s2[i]]);
        assert multiset(s2') == multiset(s2) - multiset([s2[i]]);
        assert multiset(s1[1..]) == multiset(s1) - multiset([s1[0]]);
        assert multiset(s1[1..]) == multiset(s2');
        
        CountPermutation(s1[1..], s2', value);
        
        if s1[0] == value {
            assert count(s1, value) == 1 + count(s1[1..], value);
            assert s2[i] == value;
            CountSplit(s2, i, value);
            assert count(s2, value) == count(s2[..i], value) + 1 + count(s2[i+1..], value);
            CountConcat(s2[..i], s2[i+1..], value);
            assert count(s2', value) == count(s2[..i], value) + count(s2[i+1..], value);
            assert count(s2, value) == 1 + count(s2', value);
        } else {
            assert count(s1, value) == count(s1[1..], value);
            assert s2[i] != value;
            CountSplit(s2, i, value);
            assert count(s2, value) == count(s2[..i], value) + count(s2[i+1..], value);
            CountConcat(s2[..i], s2[i+1..], value);
            assert count(s2', value) == count(s2[..i], value) + count(s2[i+1..], value);
            assert count(s2, value) == count(s2', value);
        }
    }
}

lemma CountSplit(s: seq<int>, i: int, value: int)
    requires 0 <= i < |s|
    ensures count(s, value) == count(s[..i], value) + (if s[i] == value then 1 else 0) + count(s[i+1..], value)
{
    if i == 0 {
        assert s[..i] == [];
        assert count(s[..i], value) == 0;
        assert s == [s[0]] + s[1..];
        assert count(s, value) == (if s[0] == value then 1 else 0) + count(s[1..], value);
    } else {
        assert s[..i] == [s[0]] + s[1..i];
        assert count(s[..i], value) == (if s[0] == value then 1 else 0) + count(s[1..i], value);
        assert s[1..][..i-1] == s[1..i];
        assert s[1..][i-1] == s[i];
        assert s[1..][(i-1)+1..] == s[i+1..];
        CountSplit(s[1..], i-1, value);
        assert count(s[1..], value) == count(s[1..][..i-1], value) + (if s[1..][i-1] == value then 1 else 0) + count(s[1..][(i-1)+1..], value);
        assert count(s[1..], value) == count(s[1..i], value) + (if s[i] == value then 1 else 0) + count(s[i+1..], value);
        assert count(s, value) == (if s[0] == value then 1 else 0) + count(s[1..], value);
        assert count(s, value) == (if s[0] == value then 1 else 0) + count(s[1..i], value) + (if s[i] == value then 1 else 0) + count(s[i+1..], value);
        assert count(s, value) == count(s[..i], value) + (if s[i] == value then 1 else 0) + count(s[i+1..], value);
    }
}

lemma CountConcat(s1: seq<int>, s2: seq<int>, value: int)
    ensures count(s1 + s2, value) == count(s1, value) + count(s2, value)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        CountConcat(s1[1..], s2, value);
    }
}
// </vc-helpers>

// <vc-spec>
method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    //ensures IsOrderPreserved(arr[..], old(arr[..]))
    // Number of zeros is preserved
// </vc-spec>
// <vc-code>
{
    var writeIndex := 0;
    var readIndex := 0;
    
    while readIndex < arr.Length
        invariant 0 <= writeIndex <= readIndex <= arr.Length
        invariant forall i :: 0 <= i < writeIndex ==> arr[i] != 0
        invariant forall i :: writeIndex <= i < readIndex ==> arr[i] == 0
        invariant multiset(arr[..]) == multiset(old(arr[..]))
        invariant forall i :: readIndex <= i < arr.Length ==> arr[i] == old(arr[i])
        invariant forall n, m :: 0 <= n < m < writeIndex ==> 
                (exists on, om :: 0 <= on < om < arr.Length && 
                arr[n] == old(arr[on]) && arr[m] == old(arr[om]) && 
                old(arr[on]) != 0 && old(arr[om]) != 0)
        invariant forall n, m :: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 && n < readIndex && m < readIndex ==>
                exists k, l :: 0 <= k < l < writeIndex && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    {
        if arr[readIndex] != 0 {
            if writeIndex != readIndex {
                swap(arr, writeIndex, readIndex);
            }
            writeIndex := writeIndex + 1;
        }
        readIndex := readIndex + 1;
    }
    
    assert forall i :: 0 <= i < writeIndex ==> arr[i] != 0;
    assert forall i :: writeIndex <= i < arr.Length ==> arr[i] == 0;
}
// </vc-code>

