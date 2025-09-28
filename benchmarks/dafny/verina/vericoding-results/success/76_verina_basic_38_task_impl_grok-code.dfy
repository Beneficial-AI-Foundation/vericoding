// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllCharactersSame(s: seq<char>) returns (result: bool)
    requires true
    ensures result ==> (forall i: int, j: int :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j])
    ensures !result ==> (|s| > 0 && exists i: int :: 0 <= i < |s| && s[i] != s[0])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed syntax, added loop invariants for verification */
  if |s| == 0 {
    result := true;
  } else {
    var allSame := true;
    var i := 1;
    while i < |s|
      invariant 1 <= i <= |s|
      invariant allSame ==> (forall k :: 0 <= k < i ==> s[k] == s[0])
      invariant !allSame ==> exists k :: 0 <= k < i && s[k] != s[0]
    {
      if s[i] != s[0] {
        allSame := false;
      }
      i := i + 1;
    }
    result := allSame;
  }
}
// </vc-code>
