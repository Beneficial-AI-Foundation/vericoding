

// <vc-helpers>
// no helpers needed
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
    invariant forall k :: 0 <= k < i ==> v[2*k] == x && v[2*k + 1] == s[k]
    decreases |s| - i
  {
    v := v + [x, s[i]];
    i := i + 1;
  }
}
// </vc-code>

