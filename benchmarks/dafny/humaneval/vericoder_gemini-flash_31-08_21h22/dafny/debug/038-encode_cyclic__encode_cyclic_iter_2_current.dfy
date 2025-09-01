

// <vc-helpers>

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
    var res_arr := new int[|s|];
    var i := 0;
    while i + 3 <= |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i && k % 3 == 0 ==> res_arr[k] == s[k + 1]
        invariant forall k :: 0 <= k < i && k % 3 == 1 ==> res_arr[k] == s[k + 1]
        invariant forall k :: 0 <= k < i && k % 3 == 2 ==> res_arr[k] == s[k - 2]
    {
        res_arr[i] := s[i + 1]; // i % 3 == 0
        res_arr[i + 1] := s[i + 2]; // i % 3 == 1
        res_arr[i + 2] := s[i]; // i % 3 == 2
        i := i + 3;
    }

    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < (|s| - (|s| % 3)) && k % 3 == 0 ==> res_arr[k] == s[k + 1]
        invariant forall k :: 0 <= k < (|s| - (|s| % 3)) && k % 3 == 1 ==> res_arr[k] == s[k + 1]
        invariant forall k :: 0 <= k < (|s| - (|s| % 3)) && k % 3 == 2 ==> res_arr[k] == s[k - 2]
        invariant forall k :: (|s| - (|s| % 3)) <= k < i ==> res_arr[k] == s[k]
    {
        res_arr[i] := s[i];
        i := i + 1;
    }
    return res_arr[..];
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