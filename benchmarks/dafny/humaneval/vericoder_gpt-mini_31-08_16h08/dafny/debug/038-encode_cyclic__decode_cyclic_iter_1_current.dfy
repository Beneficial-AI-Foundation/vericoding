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
// (no helpers required)
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
  var n := |s|;
  var a := new int[n];
  var limit := n - n % 3;
  var b := 0;
  while b < limit
    invariant 0 <= b <= limit
    invariant forall j :: 0 <= j < b ==>
      (if j % 3 == 0 then a[j] == s[j+2] else a[j] == s[j-1])
  {
    a[b] := s[b+2];
    a[b+1] := s[b];
    a[b+2] := s[b+1];
    b := b + 3;
  }
  var i := limit;
  while i < n
    invariant limit <= i <= n
    invariant forall j :: 0 <= j < limit ==>
      (if j % 3 == 0 then a[j] == s[j+2] else a[j] == s[j-1])
    invariant forall j :: limit <= j < i ==> a[j] == s[j]
  {
    a[i] := s[i];
    i := i + 1;
  }
  res := a[..];
}
// </vc-code>

