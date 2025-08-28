// <vc-helpers>
lemma mod_arithmetic_helper(i: int, n: int)
    requires n > 0
    requires i >= 0
    ensures (i % n) < n
{
}

lemma bounds_helper(s: seq<int>, i: int)
    requires 0 <= i < |s| - |s| % 3
    requires i % 3 == 0
    ensures i + 1 < |s|
{
    assert |s| % 3 >= 0;
    assert |s| % 3 < 3;
    if |s| % 3 == 0 {
        assert i < |s|;
        assert i + 1 < |s|;
    } else if |s| % 3 == 1 {
        assert i < |s| - 1;
        assert i + 1 < |s|;
    } else {
        assert i < |s| - 2;
        assert i + 1 < |s|;
    }
}

lemma bounds_helper2(s: seq<int>, i: int)
    requires 0 <= i < |s| - |s| % 3
    requires i % 3 == 1
    ensures i + 1 < |s|
{
    assert |s| % 3 >= 0;
    assert |s| % 3 < 3;
    if |s| % 3 == 0 {
        assert i < |s|;
        assert i + 1 < |s|;
    } else if |s| % 3 == 1 {
        assert i < |s| - 1;
        assert i + 1 < |s|;
    } else {
        assert i < |s| - 2;
        assert i + 1 < |s|;
    }
}
// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
        return [];
    }
    
    var arr := new int[|s|];
    
    var i := 0;
    while i < |s| - |s| % 3
        invariant 0 <= i <= |s| - |s| % 3
        invariant |arr[..]| == |s|
        invariant forall j :: 0 <= j < i ==> (j % 3 == 0 ==> arr[j] == s[j + 1])
        invariant forall j :: 0 <= j < i ==> (j % 3 == 1 ==> arr[j] == s[j + 1])
        invariant forall j :: 0 <= j < i ==> (j % 3 == 2 ==> arr[j] == s[j - 2])
    {
        if i % 3 == 0 {
            bounds_helper(s, i);
            arr[i] := s[i + 1];
        } else if i % 3 == 1 {
            bounds_helper2(s, i);
            arr[i] := s[i + 1];
        } else {
            assert i % 3 == 2;
            assert i >= 2;
            arr[i] := s[i - 2];
        }
        i := i + 1;
    }
    
    while i < |s|
        invariant |s| - |s| % 3 <= i <= |s|
        invariant |arr[..]| == |s|
        invariant forall j :: 0 <= j < |s| - |s| % 3 ==> (j % 3 == 0 ==> arr[j] == s[j + 1])
        invariant forall j :: 0 <= j < |s| - |s| % 3 ==> (j % 3 == 1 ==> arr[j] == s[j + 1])
        invariant forall j :: 0 <= j < |s| - |s| % 3 ==> (j % 3 == 2 ==> arr[j] == s[j - 2])
        invariant forall j :: |s| - |s| % 3 <= j < i ==> arr[j] == s[j]
    {
        arr[i] := s[i];
        i := i + 1;
    }
    
    return arr[..];
}
// </vc-code>

method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
{
  assume{:axiom} false;
}