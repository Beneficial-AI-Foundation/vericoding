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
  while i < |s| && ok
    invariant 0 <= i <= |s|
    invariant ok ==> (forall j :: 0 <= j < i && j % 2 == 0 ==> s[j] != 'L')
    invariant ok ==> (forall j :: 0 <= j < i && j % 2 == 1 ==> s[j] != 'R')
    invariant EasilyPlayable(s) ==> ok
    decreases |s| - i
  {
    assert 0 <= i < |s|;
    assert EasilyPlayable(s) ==> (i % 2 == 0 ==> s[i] != 'L');
    assert EasilyPlayable(s) ==> (i % 2 == 1 ==> s[i] != 'R');
    var safe := (i % 2 == 0 ==> s[i] != 'L') && (i % 2 == 1 ==> s[i] != 'R');
    ok := ok && safe;
    i := i + 1;
  }
  if ok {
    assert !(i < |s| && ok);
    assert i >= |s|;
    assert i == |s|;
    assert (forall j :: 0 <= j < |s| && j % 2 == 0 ==> s[j] != 'L');
    assert (forall j :: 0 <= j < |s| && j % 2 == 1 ==> s[j] != 'R');
  }
  if ok {
    result := "Yes";
  } else {
    result := "No";
  }
  assert (EasilyPlayable(s) ==> ok);
  assert (ok ==> EasilyPlayable(s));
  assert (result == "Yes") <==> EasilyPlayable(s);
}
// </vc-code>

