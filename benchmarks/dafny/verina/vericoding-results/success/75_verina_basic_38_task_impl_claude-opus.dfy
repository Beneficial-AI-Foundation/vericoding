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
    return;
  }
  
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] == s[0]
  {
    if s[i] != s[0] {
      result := false;
      return;
    }
    i := i + 1;
  }
  
  result := true;
}
// </vc-code>
