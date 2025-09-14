// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
{
  if |s| <= 1 {
    result := true;
  } else {
    result := forall i :: 1 <= i < |s| ==> s[i] == s[0];
  }
}
// </vc-code>
