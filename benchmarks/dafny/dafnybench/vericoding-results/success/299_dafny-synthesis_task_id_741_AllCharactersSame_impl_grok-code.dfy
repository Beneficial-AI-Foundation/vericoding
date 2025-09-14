

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
    var allSame := true;
    var i := 1;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant allSame ==> forall k :: 0 <= k < i ==> s[k] == s[0]
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

