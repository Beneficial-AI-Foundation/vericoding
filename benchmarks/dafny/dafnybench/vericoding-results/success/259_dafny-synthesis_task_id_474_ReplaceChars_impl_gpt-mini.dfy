

// <vc-helpers>
// No helpers needed for this implementation.
// </vc-helpers>

// <vc-spec>
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var a := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> a[j] == (if s[j] == oldChar then newChar else s[j])
  {
    a[i] := if s[i] == oldChar then newChar else s[i];
    i := i + 1;
  }
  v := a[..];
  // relate lengths
  assert a.Length == |s|;
  assert |v| == a.Length;
  assert |v| == |s|;
  // relate characters
  assert forall k :: 0 <= k < |s| ==> v[k] == (if s[k] == oldChar then newChar else s[k]);
}
// </vc-code>

