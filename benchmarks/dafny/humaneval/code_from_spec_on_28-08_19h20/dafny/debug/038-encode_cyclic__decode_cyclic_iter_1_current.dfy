method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method decode_cyclic(s: seq<int>) returns (res: seq<int>)
Decode data. Ensures: returns the correct size/count; the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 1])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
// </vc-spec>
// <vc-code>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 1])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
{
    res := new int[|s|];
    var i := 0;
    
    while i < |s| - |s| % 3
        invariant 0 <= i <= |s| - |s| % 3
        invariant |res| == |s|
        invariant forall j :: 0 <= j < i ==> (j % 3 == 0 ==> res[j] == s[j + 2])
        invariant forall j :: 0 <= j < i ==> (j % 3 == 1 ==> res[j] == s[j - 1])
        invariant forall j :: 0 <= j < i ==> (j % 3 == 2 ==> res[j] == s[j - 1])
    {
        if i % 3 == 0 {
            res[i] := s[i + 2];
        } else if i % 3 == 1 {
            res[i] := s[i - 1];
        } else {
            res[i] := s[i - 1];
        }
        i := i + 1;
    }
    
    while i < |s|
        invariant |s| - |s| % 3 <= i <= |s|
        invariant |res| == |s|
        invariant forall j :: 0 <= j < |s| - |s| % 3 ==> (j % 3 == 0 ==> res[j] == s[j + 2])
        invariant forall j :: 0 <= j < |s| - |s| % 3 ==> (j % 3 == 1 ==> res[j] == s[j - 1])
        invariant forall j :: 0 <= j < |s| - |s| % 3 ==> (j % 3 == 2 ==> res[j] == s[j - 1])
        invariant forall j :: |s| - |s| % 3 <= j < i ==> (res[j] == s[j])
    {
        res[i] := s[i];
        i := i + 1;
    }
}
// </vc-code>
