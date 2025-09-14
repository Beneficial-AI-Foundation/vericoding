

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
// </vc-spec>
// <vc-code>
{
  var n := |l|;
  var a := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == l[j][|l[j]| - 1]
  {
    a[i] := l[i][|l[i]| - 1];
    i := i + 1;
  }
  r := a[..];
}
// </vc-code>

