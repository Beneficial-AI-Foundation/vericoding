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
// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>
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
  var found := false;
  if |word| >= |pattern| {
    var i := 0;
    while i <= |pattern|
      invariant 0 <= i <= |pattern| + 1
      invariant !found
    {
      var rot := RotateString(pattern, i);
      var j := 0;
      while j <= |word| - |pattern|
        invariant 0 <= j <= |word| - |pattern| + 1
      {
        if word[j..j+|pattern|] == rot { found := true; }
        j := j + 1;
      }
      i := i + 1;
      if found { break; }
    }
  }
  result := found;
}
// </vc-code>

