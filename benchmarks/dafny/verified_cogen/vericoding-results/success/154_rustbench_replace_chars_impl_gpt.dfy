// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ReplaceChar(c: char, oldc: char, newc: char): char { if c == oldc then newc else c }
// </vc-helpers>

// <vc-spec>
method ReplaceChars(s: array<char>, old_char: char, new_char: char) returns (result: array<char>)
    ensures
        result.Length == s.Length
    ensures
        forall i :: 0 <= i < result.Length ==> result[i] == (if s[i] == old_char then new_char else s[i])
// </vc-spec>
// <vc-code>
{
  result := new char[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant result.Length == s.Length
    invariant forall j :: 0 <= j < i ==> result[j] == (if s[j] == old_char then new_char else s[j])
    decreases s.Length - i
  {
    result[i] := if s[i] == old_char then new_char else s[i];
    i := i + 1;
  }
}
// </vc-code>
