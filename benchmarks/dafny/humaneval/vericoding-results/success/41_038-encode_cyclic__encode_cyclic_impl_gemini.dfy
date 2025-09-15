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
  var arr := new int[|s|];
  var i := 0;
  var limit := |s| - |s| % 3;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i && j < limit && j % 3 == 0 ==> arr[j] == s[j + 1]
    invariant forall j :: 0 <= j < i && j < limit && j % 3 == 1 ==> arr[j] == s[j + 1]
    invariant forall j :: 0 <= j < i && j < limit && j % 3 == 2 ==> arr[j] == s[j - 2]
    invariant forall j :: limit <= j < i ==> arr[j] == s[j]
  {
    if i < limit {
      if i % 3 == 0 {
        arr[i] := s[i+1];
      } else if i % 3 == 1 {
        arr[i] := s[i+1];
      } else { // i % 3 == 2
        arr[i] := s[i-2];
      }
    } else {
      arr[i] := s[i];
    }
    i := i + 1;
  }

  res := arr[..];
}
// </vc-code>
