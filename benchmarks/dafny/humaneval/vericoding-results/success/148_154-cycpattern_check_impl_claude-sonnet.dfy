// <vc-preamble>
function IsSubstring(s: string, sub: string) : bool
{
  |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}
function RotateString(s: string, n: nat): string
  requires 0 <= n <= |s|
{
  s[n..] + s[..n]
}
// </vc-preamble>

// <vc-helpers>
function CheckAllRotations(word: string, pattern: string, i: nat): bool
  requires i <= |pattern|
  decreases |pattern| - i
{
  if i > |pattern| then false
  else if IsSubstring(word, RotateString(pattern, i)) then true
  else if i == |pattern| then false
  else CheckAllRotations(word, pattern, i + 1)
}

lemma CheckAllRotationsCorrect(word: string, pattern: string, i: nat)
  requires i <= |pattern|
  ensures CheckAllRotations(word, pattern, i) <==> exists j :: i <= j <= |pattern| && IsSubstring(word, RotateString(pattern, j))
  decreases |pattern| - i
{
  if i > |pattern| {
  } else if IsSubstring(word, RotateString(pattern, i)) {
  } else if i == |pattern| {
  } else {
    CheckAllRotationsCorrect(word, pattern, i + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)

  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
// </vc-spec>
// <vc-code>
{
  var found := CheckAllRotations(word, pattern, 0);
  CheckAllRotationsCorrect(word, pattern, 0);
  result := found;
}
// </vc-code>
