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
function IsSubstringUtil(s: string, sub: string) : bool
{
  |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}

function RotateStringUtil(s: string, n: nat): string
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
    invariant 0 <= i <= |pattern|
    invariant found ==> exists j :: 0 <= j < i && IsSubstringUtil(word, RotateStringUtil(pattern, j as nat))
    invariant !found ==> (forall j :: 0 <= j < i ==> !IsSubstringUtil(word, RotateStringUtil(pattern, j as nat)))
  {
    if i == |pattern| { // Handle the case of the original pattern itself
      rotatedPattern := pattern;
    } else {
      rotatedPattern := RotateStringUtil(pattern, i as nat);
    }
    
    if IsSubstringUtil(word, rotatedPattern)
    {
      found := true;
      i := |pattern| + 1; // Terminate loop
    } else {
      i := i + 1;
    }
  }
  result := found;
}
// </vc-code>

