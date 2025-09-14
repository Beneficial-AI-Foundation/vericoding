

// <vc-helpers>
function ReplaceChar(s: string, ch: char, idx: int): string
  requires 0 <= idx <= |s|
  ensures |ReplaceChar(s, ch, idx)| == |s|
  ensures forall i :: 0 <= i < |s| ==> 
    (i < idx && s[i] == ' ' ==> ReplaceChar(s, ch, idx)[i] == ch) &&
    (i < idx && s[i] != ' ' ==> ReplaceChar(s, ch, idx)[i] == s[i]) &&
    (i >= idx ==> ReplaceChar(s, ch, idx)[i] == s[i])
{
  if idx == 0 then
    s
  else
    var prev := ReplaceChar(s, ch, idx-1);
    if s[idx-1] == ' ' then
      prev[..idx-1] + [ch] + prev[idx..]
    else
      prev
}

lemma ReplaceCharPreservesLength(s: string, ch: char, idx: int)
  requires 0 <= idx <= |s|
  ensures |ReplaceChar(s, ch, idx)| == |s|
{
}

lemma ReplaceCharCorrectness(s: string, ch: char, idx: int)
  requires 0 <= idx <= |s|
  ensures forall i :: 0 <= i < |s| ==> 
    (i < idx && s[i] == ' ' ==> ReplaceChar(s, ch, idx)[i] == ch) &&
    (i < idx && s[i] != ' ' ==> ReplaceChar(s, ch, idx)[i] == s[i]) &&
    (i >= idx ==> ReplaceChar(s, ch, idx)[i] == s[i])
{
}
// </vc-helpers>

// <vc-spec>
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  v := ReplaceChar(s, ch, |s|);
}
// </vc-code>

