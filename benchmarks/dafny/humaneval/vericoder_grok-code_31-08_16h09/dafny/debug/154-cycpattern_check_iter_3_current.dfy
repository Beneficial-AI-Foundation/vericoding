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
// <vc-helpers>

// </vc-helpers>
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
      invariant !found ==> forall k :: 0 <= k < i ==> !IsSubstring(word, RotateString(pattern, k))
    {
      var rot := RotateString(pattern, i);
      if IsSubstring(word, rot) {
        found := true;
      }
      i := i + 1;
    }
  }
  result := found;
}
// </vc-code>

