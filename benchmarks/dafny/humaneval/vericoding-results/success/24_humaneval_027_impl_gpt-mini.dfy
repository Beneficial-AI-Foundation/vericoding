// <vc-preamble>

predicate IsLowercase(c: char) {
    'a' <= c <= 'z'
}

predicate IsUppercase(c: char) {
    'A' <= c <= 'Z'
}

function FlipChar(c: char): char {
    if IsLowercase(c) then c - 'a' + 'A'
    else if IsUppercase(c) then c - 'A' + 'a'
    else c
}

predicate ValidFlipCase(s: string, result: string) {
    |result| == |s| &&
    forall i :: 0 <= i < |s| ==> result[i] == FlipChar(s[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): construct string from char array and prove length and character equality */
method ArrayCharsToStringProps(a: array<char>) returns (s: string)
  ensures |s| == a.Length
  ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
{
  s := a[..];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> s[j] == a[j]
  {
    assert s[i] == a[i];
    i := i + 1;
  }
  assert |s| == a.Length;
  assert forall j :: 0 <= j < a.Length ==> s[j] == a[j];
}

// </vc-helpers>

// <vc-spec>
method flip_case(s: string) returns (result: string)
    ensures ValidFlipCase(s, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): populate array with flipped chars, convert to string using helper */
{
  var n := |s|;
  var a := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == FlipChar(s[j])
  {
    a[i] := FlipChar(s[i]);
    i := i + 1;
  }
  result := ArrayCharsToStringProps(a);
}

// </vc-code>
