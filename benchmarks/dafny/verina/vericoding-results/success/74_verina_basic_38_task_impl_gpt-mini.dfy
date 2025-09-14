// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): check all elements equal to first */
function AllEqualToFirst(s: seq<char>): bool { if |s| == 0 then true else forall i: int :: 0 <= i < |s| ==> s[i] == s[0] }
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(s: seq<char>) returns (result: bool)
    requires true
    ensures result ==> (forall i: int, j: int :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j])
    ensures !result ==> (|s| > 0 && exists i: int :: 0 <= i < |s| && s[i] != s[0])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop to always advance i and added invariant for bad index */
  if |s| == 0 {
    result := true;
    return;
  }
  var i := 0;
  var found := false;
  var bad := 0;
  while i < |s| && !found
    invariant 0 <= i <= |s|
    invariant !found ==> (forall j: int :: 0 <= j < i ==> s[j] == s[0])
    invariant found ==> 0 <= bad < |s| && s[bad] != s[0]
    decreases |s| - i
  {
    if s[i] != s[0] {
      bad := i;
      found := true;
      i := i + 1;
    } else {
      i := i + 1;
    }
  }
  if found {
    result := false;
    assert |s| > 0;
    assert 0 <= bad < |s|;
    assert s[bad] != s[0];
  } else {
    result := true;
  }
}
// </vc-code>
