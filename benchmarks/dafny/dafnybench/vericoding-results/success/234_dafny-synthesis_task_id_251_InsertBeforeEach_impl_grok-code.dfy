

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
// </vc-spec>
// <vc-code>
{
  var result := new string[2 * |s|];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> result[2 * j] == x && result[2 * j + 1] == s[j]
  {
    result[2 * i] := x;
    result[2 * i + 1] := s[i];
  }
  return result[..];
}
// </vc-code>

