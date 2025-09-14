

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  v := "";
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> (s[j] == ' ' ==> v[j] == ch) && (s[j] != ' ' ==> v[j] == s[j])
    decreases |s| - i
  {
    if s[i] == ' ' {
      v := v + [ch];
    } else {
      v := v + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

