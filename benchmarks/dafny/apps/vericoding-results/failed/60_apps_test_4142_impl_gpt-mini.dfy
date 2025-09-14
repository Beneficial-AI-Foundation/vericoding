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
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" <==> EasilyPlayable(s)
    ensures result in
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var ok := true;
  ghost var w: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant ok ==> (forall j :: 0 <= j < i ==> (j % 2 == 0 ==> s[j] != 'L') && (j % 2 == 1 ==> s[j] != 'R'))
    invariant !ok ==> 0 <= w < i && ((w % 2 == 0 && s[w] == 'L') || (w % 2 == 1 && s[w] == 'R'))
  {
    if i % 2 == 0 {
      if s[i] == 'L' {
        w := i;
        ok := false;
      }
    } else {
      if s[i] == 'R' {
        w := i;
        ok := false;
      }
    }
    i := i + 1;
  }
  if ok {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

