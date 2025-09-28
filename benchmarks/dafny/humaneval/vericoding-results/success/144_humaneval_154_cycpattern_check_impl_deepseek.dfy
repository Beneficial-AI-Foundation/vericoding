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

function IsRotationSubstring(s: string, p: string, i: int): bool
  requires 0 <= i <= |p|
{
  IsSubstring(s, RotateString(p, i))
}
predicate HasMatchingRotation(word: string, pattern: string)
{
  exists i | 0 <= i <= |pattern| :: IsSubstring(word, RotateString(pattern, i))
}
lemma RotationCoverage(word: string, pattern: string)
  ensures HasMatchingRotation(word, pattern) == (exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i)))
{
}

// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)

  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
// </vc-spec>
// <vc-code>
{
    var i := 0;
    result := false;
    
    while i <= |pattern|
      invariant 0 <= i <= |pattern| + 1
      invariant !result ==> forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
      invariant result ==> IsSubstring(word, RotateString(pattern, i-1))
    {
        if IsSubstring(word, RotateString(pattern, i)) {
            result := true;
            break;
        }
        i := i + 1;
    }
  }
// </vc-code>
