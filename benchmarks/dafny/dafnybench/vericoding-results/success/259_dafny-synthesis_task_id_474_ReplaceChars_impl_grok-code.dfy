

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var result: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> (if s[k] == oldChar then result[k] == newChar else result[k] == s[k])
  {
    if s[i] == oldChar {
      result := result + [newChar];
    } else {
      result := result + [s[i]];
    }
    i := i + 1;
  }
  return result;
}
// </vc-code>

