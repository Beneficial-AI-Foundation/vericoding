// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ArraySliceIndex(arr: array<int>, n: int)
  requires arr.Length == n
  ensures forall i :: 0 <= i < n ==> arr[..][i] == arr[i]
{
}

// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires |a| > 0
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arr.Length == n
    invariant forall j :: 0 <= j < i ==> arr[j] == a[j] % b[j]
  {
    arr[i] := a[i] % b[i];
    i := i + 1;
  }
  result := arr[..];
}

// </vc-code>
