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
/* helper modified by LLM (iteration 4): predicates capturing existence or absence of a matching rotation */
predicate ExistsRotationSubstring(word: string, pattern: string)
{
  exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
}
predicate ForallNoRotationSubstring(word: string, pattern: string)
{
  forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
}
// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)

  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): search all rotations with loop invariants; removed quantifier statements to avoid warnings */
  var n := |pattern|;
  var i := 0;
  var found := false;
  var w := 0;
  while i <= n
    invariant 0 <= i && i <= n + 1
    invariant 0 <= w && w <= n
    invariant found ==> (0 <= w && w <= n && IsSubstring(word, RotateString(pattern, w)))
    invariant !found ==> (forall j :: 0 <= j && j < i ==> !IsSubstring(word, RotateString(pattern, j)))
  {
    if !found && IsSubstring(word, RotateString(pattern, i)) {
      found := true;
      w := i;
    }
    i := i + 1;
  }
  result := found;
  if result {
    assert 0 <= w && w <= |pattern|;
    assert IsSubstring(word, RotateString(pattern, w));
  } else {
    assert !found;
    assert i == n + 1;
    // From the invariant with i = n + 1, it follows that all j in [0..n] do not match.
  }
}
// </vc-code>
