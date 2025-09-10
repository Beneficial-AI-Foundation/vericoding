method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
{
    // impl-start
    res := s;
    var i := 0;
    while i + 2 < |s|
        // invariants-start
        invariant 0 <= i <= |s|
        invariant |s| == |res|
        invariant i % 3 == 0
        invariant forall j :: i <= j < |s| ==> (res[j] == s[j])
        invariant forall j :: 0 <= j < i ==> (j % 3 == 0 ==> res[j] == s[j + 1])
        invariant forall j :: 0 <= j < i ==> (j % 3 == 1 ==> res[j] == s[j + 1])
        invariant forall j :: 0 <= j < i ==> (j % 3 == 2 ==> res[j] == s[j - 2])
        // invariants-end
    {
        res := res[i := s[i + 1]];
        res := res[i + 1 := s[i + 2]];
        res := res[i + 2 := s[i]];
        i := i + 3;
    }
    // impl-end
}

method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
{
    // impl-start
    var intermediate := encode_cyclic(s);
    res := encode_cyclic(intermediate);
    // impl-end
}
