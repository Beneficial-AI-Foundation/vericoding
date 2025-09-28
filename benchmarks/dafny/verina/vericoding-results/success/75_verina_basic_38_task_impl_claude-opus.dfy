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
    result := true;
    var first := s[0];
    var i := 1;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant result <==> (forall j :: 0 <= j < i ==> s[j] == first)
    {
      if s[i] != first {
        result := false;
        break;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
