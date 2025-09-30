

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
// </vc-spec>
// <vc-code>
{
  v := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < i ==> v[2*j] == x && v[2*j + 1] == s[j]
  {
    v := v + [x, s[i]];
    i := i + 1;
  }
}
// </vc-code>

