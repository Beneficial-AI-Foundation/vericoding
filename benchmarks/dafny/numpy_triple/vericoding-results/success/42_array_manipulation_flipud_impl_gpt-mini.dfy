// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function revIndex(n: int, i: int): int
  requires 0 <= i < n
  ensures 0 <= revIndex(n, i) < n
{
  n - 1 - i
}
// </vc-helpers>

// <vc-spec>
method flipud(m: seq<real>) returns (result: seq<real>)
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
{
  var n := |m|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == m[n - 1 - j]
  {
    a[i] := m[n - 1 - i];
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
