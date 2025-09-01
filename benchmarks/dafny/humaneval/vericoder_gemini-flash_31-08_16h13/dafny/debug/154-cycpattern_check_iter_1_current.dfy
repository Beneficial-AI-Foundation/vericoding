function IsSubstring(s: string, sub: string) : bool
{
  |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}
function RotateString(s: string, n: nat): string
  requires 0 <= n <= |s|
{
  s[n..] + s[..n]
}

// <vc-helpers>
function method IsSubstring(s: string, sub: string) : bool
{
  |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}

function method RotateString(s: string, n: nat): string
  requires 0 <= n <= |s|
{
  s[n..] + s[..n]
}
// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)
  // post-conditions-start
  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var rotatedPattern: string;
  var found: bool := false;
  var i: int := 0;

  while i <= |pattern|
    invariant 0 <= i <= |pattern| + 1
    invariant found ==> exists j :: 0 <= j < i && IsSubstring(word, RotateString(pattern, j))
    invariant !found ==> forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
  {
    rotatedPattern := RotateString(pattern, i);
    if IsSubstring(word, rotatedPattern)
    {
      found := true;
      break;
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>

