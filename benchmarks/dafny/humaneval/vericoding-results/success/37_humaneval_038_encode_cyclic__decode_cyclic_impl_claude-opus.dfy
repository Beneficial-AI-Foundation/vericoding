// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)

    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
// </vc-spec>
// <vc-code>
{
  res := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res| == i
    invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 0 ==> res[j] == s[j + 2]
    invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 1 ==> res[j] == s[j - 1]
    invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 2 ==> res[j] == s[j - 2]
    invariant forall j :: |s| - |s| % 3 <= j < i ==> res[j] == s[j]
  {
    if i < |s| - |s| % 3 {
      if i % 3 == 0 {
        res := res + [s[i + 2]];
      } else if i % 3 == 1 {
        res := res + [s[i - 1]];
      } else {
        res := res + [s[i - 2]];
      }
    } else {
      res := res + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
