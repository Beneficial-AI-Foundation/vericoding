

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var a := new string[2 * n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[2*j] == x && a[2*j + 1] == s[j]
  {
    a[2*i] := x;
    a[2*i + 1] := s[i];
    i := i + 1;
  }
  v := a[..];
}
// </vc-code>

