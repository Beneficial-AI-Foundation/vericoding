//ATOM
lemma swap_preserves_multiset_helper(s: seq<int>, i: int, j: int)
    requires 0 <= i < j < |s|
    ensures multiset(s[..j+1]) == multiset(s[..i]) + multiset(s[i+1..j]) + multiset{s[j]} + multiset{s[i]}
{
    var fst := s[..i];
    var snd := s[i+1..j];
    
    assert s[..j+1] == s[..i] + [s[i]] + s[i+1..j] + [s[j]];
    assert multiset(s[..j+1]) == multiset(s[..i]) + multiset{s[i]} + multiset(s[i+1..j]) + multiset{s[j]};
}

//ATOM
lemma swap_preserves_multiset(s1: seq<int>, s2: seq<int>, i: int, j: int)
    requires 0 <= i < j < |s1| == |s2|
    requires forall x :: 0 <= x < |s1| && x != i && x != j ==> s1[x] == s2[x]
    requires s1[i] == s2[j]
    requires s1[j] == s2[i]
    ensures multiset(s1) == multiset(s2)
{
    assert s1[..j+1] == s1[..i] + [s1[i]] + s1[i+1..j] + [s1[j]];
    assert s2[..j+1] == s2[..i] + [s2[i]] + s2[i+1..j] + [s2[j]];
    assert s1[..i] == s2[..i];
    assert s1[i+1..j] == s2[i+1..j];
    assert s1[j+1..] == s2[j+1..];
    
    calc {
        multiset(s1);
        multiset(s1[..j+1]) + multiset(s1[j+1..]);
        multiset(s1[..i]) + multiset{s1[i]} + multiset(s1[i+1..j]) + multiset{s1[j]} + multiset(s1[j+1..]);
        multiset(s2[..i]) + multiset{s2[j]} + multiset(s2[i+1..j]) + multiset{s2[i]} + multiset(s2[j+1..]);
        multiset(s2[..i]) + multiset{s2[i]} + multiset(s2[i+1..j]) + multiset{s2[j]} + multiset(s2[j+1..]);
        multiset(s2[..j+1]) + multiset(s2[j+1..]);
        multiset(s2);
    }
}

//IMPL sort_seq
method sort_seq(s: seq<int>) returns (ret: seq<int>)
    ensures forall i, j :: 0 <= i < j < |ret| ==> ret[i] <= ret[j]
    ensures |ret| == |s|
    ensures multiset(s) == multiset(ret)
{
    /* code modified by LLM (iteration 1): Implemented bubble sort algorithm */
    ret := s;
    var n := |ret|;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |ret| == |s|
        invariant multiset(s) == multiset(ret)
        invariant forall x, y :: 0 <= x < y < i ==> ret[x] <= ret[y]
        invariant forall x, y :: 0 <= x < i && i <= y < |ret| ==> ret[x] <= ret[y]
        decreases n - i
    {
        var j := i + 1;
        while j < n
            invariant i + 1 <= j <= n
            invariant |ret| == |s|
            invariant multiset(s) == multiset(ret)
            invariant forall x, y :: 0 <= x < y < i ==> ret[x] <= ret[y]
            invariant forall x, y :: 0 <= x < i && i <= y < |ret| ==> ret[x] <= ret[y]
            invariant forall k :: i < k < j ==> ret[i] <= ret[k]
            decreases n - j
        {
            if ret[j] < ret[i] {
                var old_ret := ret;
                ret := ret[i := ret[j]][j := old_ret[i]];
                swap_preserves_multiset(old_ret, ret, i, j);
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

//IMPL unique_sorted
method unique_sorted(s: seq<int>) returns (result: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall i :: 0 <= i < |result| ==> s[i] in s
    ensures forall i :: 0 <= i < |s| ==> s[i] in result
{
    /* code modified by LLM (iteration 1): Implemented unique logic for sorted sequence */
    result := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall x, y :: 0 <= x < y < |result| ==> result[x] < result[y]
        invariant forall x :: 0 <= x < |result| ==> result[x] in s
        invariant forall x :: 0 <= x < i ==> s[x] in result
        decreases |s| - i
    {
        if |result| == 0 || result[|result| - 1] != s[i] {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}

//IMPL unique
method unique(s: seq<int>) returns (result: seq<int>)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall i :: 0 <= i < |result| ==> result[i] in s
    ensures forall i :: 0 <= i < |s| ==> s[i] in result
{
    /* code modified by LLM (iteration 1): Implemented unique by first sorting then removing duplicates */
    var sorted := sort_seq(s);
    result := unique_sorted(sorted);
}