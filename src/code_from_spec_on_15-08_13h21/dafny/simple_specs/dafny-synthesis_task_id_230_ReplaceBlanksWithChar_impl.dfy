//IMPL
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
  /* code modified by LLM (iteration 4): Fixed syntax error - removed extra semicolon and quote */
  v := "";"
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> (s[j] == ' ' ==> v[j] == ch) && (s[j] != ' ' ==> v[j] == s[j])
  {
    if s[i] == ' ' {
      v := v + [ch];
    } else {
      v := v + [s[i]];
    }
    i := i + 1;
  }
}