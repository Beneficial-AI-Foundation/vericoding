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
// No additional helpers needed for this implementation.
// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  res := [];
  for i := 0 to |s| - 1
    invariant |res| == i
    invariant forall j :: 0 <= j < i && j >= |s| - |s| % 3 ==> res[j] == s[j]
    invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 0 ==> res[j] == s[j + 2]
    invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 1 ==> res[j] == s[j - 1]
    invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 2 ==> res[j] == s[j - 1]
  {
    if i < |s| - |s| % 3 {
      if i % 3 == 0 {
        res := res + [s[i + 2]];
      } else if i % 3 == 1 {
        res := res + [s[i - 1]];
      } else {
        res := res + [s[i - 1]];
      }
    } else {
      res := res + [s[i]];
    }
  }
}
// </vc-code>

