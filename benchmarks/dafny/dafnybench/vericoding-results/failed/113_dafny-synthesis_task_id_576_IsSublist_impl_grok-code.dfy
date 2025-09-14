

// <vc-helpers>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  ensures result == (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
  if (|sub| == 0) {
    return true;
  }
  if (|sub| > |main|) {
    return false;
  }
  var i := 0;
  while i <= |main| - |sub|
    invariant 0 <= i <= |main| - |sub| + 1
    invariant forall k :: {:trigger main[k..k + |sub|]} 0 <= k < i ==> main[k..k + |sub|] != sub
  {
    if main[i..i + |main|] == sub {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

