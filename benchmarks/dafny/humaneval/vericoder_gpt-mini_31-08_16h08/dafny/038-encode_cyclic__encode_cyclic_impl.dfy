

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var arr := new int[n];
  var i := 0;
  while i + 3 <= n
    invariant 0 <= i <= n
    invariant i % 3 == 0
    invariant forall j :: 0 <= j < i ==>
      ((j % 3 == 0 ==> arr[j] == s[j+1]) &&
       (j % 3 == 1 ==> arr[j] == s[j+1]) &&
       (j % 3 == 2 ==> arr[j] == s[j-2]))
  {
    arr[i] := s[i+1];
    arr[i+1] := s[i+2];
    arr[i+2] := s[i];
    i := i + 3;
  }
  var start := n - n % 3;
  var j := start;
  while j < n
    invariant start <= j <= n
    invariant forall l :: 0 <= l < start ==>
      ((l % 3 == 0 ==> arr[l] == s[l+1]) &&
       (l % 3 == 1 ==> arr[l] == s[l+1]) &&
       (l % 3 == 2 ==> arr[l] == s[l-2]))
    invariant forall l :: start <= l < j ==> arr[l] == s[l]
  {
    arr[j] := s[j];
    j := j + 1;
  }
  res := arr[..];
}
// </vc-code>

method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
{
  assume{:axiom} false;
}