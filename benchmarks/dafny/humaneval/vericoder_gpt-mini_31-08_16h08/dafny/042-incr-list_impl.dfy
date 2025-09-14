

// <vc-helpers>
// No helper definitions needed for this proof.
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |l|;
  var a := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == l[j] + 1
  {
    a[i] := l[i] + 1;
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>

