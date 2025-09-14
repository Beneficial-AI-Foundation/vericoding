// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Fixed array length syntax in loop invariant. */
  var v_arr := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant v_arr.Length == |s|
    invariant forall k :: 0 <= k < i ==> (s[k] == oldChar ==> v_arr[k] == newChar) && (s[k] != oldChar ==> v_arr[k] == s[k])
  {
    if s[i] == oldChar {
      v_arr[i] := newChar;
    } else {
      v_arr[i] := s[i];
    }
    i := i + 1;
  }
  v := v_arr[..];
}
// </vc-code>
