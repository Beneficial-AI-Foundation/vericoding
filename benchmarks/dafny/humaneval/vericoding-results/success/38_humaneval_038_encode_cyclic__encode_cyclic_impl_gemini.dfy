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
  var a := new int[|s|];
  var i := 0;
  var limit := |s| - |s| % 3;

  while i < limit
    invariant 0 <= i <= limit
    invariant i % 3 == 0
    invariant forall j :: 0 <= j < i && j % 3 == 0 ==> a[j] == s[j + 1]
    invariant forall j :: 0 <= j < i && j % 3 == 1 ==> a[j] == s[j + 1]
    invariant forall j :: 0 <= j < i && j % 3 == 2 ==> a[j] == s[j - 2]
  {
    a[i] := s[i + 1];
    a[i + 1] := s[i + 2];
    a[i + 2] := s[i];
    i := i + 3;
  }

  while i < |s|
    invariant limit <= i <= |s|
    invariant forall j :: 0 <= j < limit && j % 3 == 0 ==> a[j] == s[j + 1]
    invariant forall j :: 0 <= j < limit && j % 3 == 1 ==> a[j] == s[j + 1]
    invariant forall j :: 0 <= j < limit && j % 3 == 2 ==> a[j] == s[j - 2]
    invariant forall j :: limit <= j < i ==> a[j] == s[j]
  {
    a[i] := s[i];
    i := i + 1;
  }
  
  res := a[..];
}
// </vc-code>
