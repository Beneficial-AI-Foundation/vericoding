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
  /* code modified by LLM (iteration 3): implemented while loop with invariants to verify postconditions and handled empty sequences */
  res := [];
  var prefix := |s| - (|s| % 3);
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res| == i
    invariant forall j :: 0 <= j < i && prefix <= j < |s| ==> res[j] == s[j]
    invariant forall j :: 0 <= j < i && j < prefix ==> (j % 3 == 0 ==> res[j] == s[j + 2]) && (j % 3 == 1 ==> res[j] == s[j - 1])
  {
    if i >= prefix {
      res := res + [s[i]];
    } else {
      if i % 3 == 0 {
        res := res + [s[i + 2]];
      } else if i % 3 == 1 {
        res := res + [s[i - 1]];
      } else {
        res := res + [s[i - 1]];
      }
    }
    i := i + 1;
  }
}
// </vc-code>
