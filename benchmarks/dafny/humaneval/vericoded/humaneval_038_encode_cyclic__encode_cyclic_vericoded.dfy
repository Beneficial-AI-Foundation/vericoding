// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 

    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var groups := |s| / 3;
  var remainder := |s| % 3;
  var result := new int[|s|];
  
  var i := 0;
  while i < groups * 3
    invariant 0 <= i <= groups * 3
    invariant i % 3 == 0
    invariant forall j :: 0 <= j < i && j % 3 == 0 ==> result[j] == s[j + 1]
    invariant forall j :: 0 <= j < i && j % 3 == 1 ==> result[j] == s[j + 1]
    invariant forall j :: 0 <= j < i && j % 3 == 2 ==> result[j] == s[j - 2]
  {
    result[i] := s[i + 1];
    result[i + 1] := s[i + 2];
    result[i + 2] := s[i];
    i := i + 3;
  }
  
  while i < |s|
    invariant groups * 3 <= i <= |s|
    invariant forall j :: 0 <= j < groups * 3 && j % 3 == 0 ==> result[j] == s[j + 1]
    invariant forall j :: 0 <= j < groups * 3 && j % 3 == 1 ==> result[j] == s[j + 1]
    invariant forall j :: 0 <= j < groups * 3 && j % 3 == 2 ==> result[j] == s[j - 2]
    invariant forall j :: groups * 3 <= j < i ==> result[j] == s[j]
  {
    result[i] := s[i];
    i := i + 1;
  }
  
  res := result[..];
}
// </vc-code>
