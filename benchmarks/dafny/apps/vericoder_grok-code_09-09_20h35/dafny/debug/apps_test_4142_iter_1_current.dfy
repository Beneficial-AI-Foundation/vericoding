predicate ValidInput(s: string)
{
    1 <= |s| <= 100 && forall i :: 0 <= i < |s| ==> s[i] in {'L', 'R', 'U', 'D'}
}

predicate EasilyPlayable(s: string)
{
    (forall i :: 0 <= i < |s| && i % 2 == 0 ==> s[i] != 'L') &&
    (forall i :: 0 <= i < |s| && i % 2 == 1 ==> s[i] != 'R')
}

// <vc-helpers>
// Empty, no additional helpers needed.
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" <==> EasilyPlayable(s)
    ensures result in
// </vc-spec>
// <vc-code>
{
  var isPlayable := true;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant isPlayable ==> forall j :: 0 <= j < i && j % 2 == 0 ==> s[j] != 'L'
    invariant isPlayable ==> forall j :: 0 <= j < i && j % 2 == 1 ==> s[j] != 'R'
  {
    if i % 2 == 0 && s[i] == 'L' {
      isPlayable := false;
    } else if i % 2 == 1 && s[i] == 'R' {
      isPlayable := false;
    }
  }
  if isPlayable {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

