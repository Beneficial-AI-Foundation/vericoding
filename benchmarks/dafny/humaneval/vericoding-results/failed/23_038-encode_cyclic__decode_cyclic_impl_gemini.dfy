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
  var a := new int[|s|];
  var limit := |s| - |s| % 3;

  var i := 0;
  while i < limit
    invariant 0 <= i <= limit
    invariant i % 3 == 0
    invariant forall k :: 0 <= k < i ==> (k % 3 == 0 ==> a[k] == s[k + 2])
    invariant forall k :: 0 <= k < i ==> (k % 3 == 1 ==> a[k] == s[k - 1])
    invariant forall k :: 0 <= k < i ==> (k % 3 == 2 ==> a[k] == s[k + 1])
    decreases limit - i
  {
    a[i] := s[i + 2];
    a[i + 1] := s[i];
    a[i + 2] := s[i + 1];
    i := i + 3;
  }

  while i < |s|
    invariant limit <= i <= |s|
    invariant forall k :: 0 <= k < limit ==> (k % 3 == 0 ==> a[k] == s[k + 2])
    invariant forall k :: 0 <= k < limit ==> (k % 3 == 1 ==> a[k] == s[k - 1])
    invariant forall k :: 0 <= k < limit ==> (k % 3 == 2 ==> a[k] == s[k + 1])
    invariant forall k :: limit <= k < i ==> a[k] == s[k]
    decreases |s| - i
  {
    a[i] := s[i];
    i := i + 1;
  }

  res := a[..];
}
// </vc-code>
