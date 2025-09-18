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
  if |s| == 0 {
    result := true;
  } else {
    var ref := s[0];
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s| && forall k :: 0 <= k < i ==> s[k] == ref
    {
      if s[i] != ref {
        result := false;
        return;
      }
      i := i + 1;
    }
    result := true;
  }
}
// </vc-code>
