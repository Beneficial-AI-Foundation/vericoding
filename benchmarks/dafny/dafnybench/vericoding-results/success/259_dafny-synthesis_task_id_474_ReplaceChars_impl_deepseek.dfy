

// <vc-helpers>
function replaceCharAt(s: string, i: int, c: char): string
  requires 0 <= i < |s|
  ensures |replaceCharAt(s, i, c)| == |s|
  ensures forall j :: 0 <= j < |s| ==> 
    (j == i ==> replaceCharAt(s, i, c)[j] == c) && 
    (j != i ==> replaceCharAt(s, i, c)[j] == s[j])
{
    s[..i] + [c] + s[i+1..]
}

ghost function ReplaceAll(s: string, oldChar: char, newChar: char): string
  ensures |ReplaceAll(s, oldChar, newChar)| == |s|
  ensures forall i :: 0 <= i < |s| ==> 
    (s[i] == oldChar ==> ReplaceAll(s, oldChar, newChar)[i] == newChar) && 
    (s[i] != oldChar ==> ReplaceAll(s, oldChar, newChar)[i] == s[i])
{
  if |s| == 0 then ""
  else if s[0] == oldChar then
    [newChar] + ReplaceAll(s[1..], oldChar, newChar)
  else
    [s[0]] + ReplaceAll(s[1..], oldChar, newChar)
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  v := s;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == |s|
    invariant forall j :: 0 <= j < i ==> 
      (s[j] == oldChar ==> v[j] == newChar) && (s[j] != oldChar ==> v[j] == s[j])
    invariant forall j :: i <= j < |s| ==> v[j] == s[j]
  {
    if s[i] == oldChar {
      v := replaceCharAt(v, i, newChar);
    }
    i := i + 1;
  }
}
// </vc-code>

