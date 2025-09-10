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
lemma EvenIndexNotL(s: string, i: int)
  requires 0 <= i < |s| && i % 2 == 0
  requires ValidInput(s)
  ensures s[i] != 'L' <==> (s[i] == 'R' || s[i] == 'U' || s[i] == 'D')
{
}

lemma OddIndexNotR(s: string, i: int)
  requires 0 <= i < |s| && i % 2 == 1
  requires ValidInput(s)
  ensures s[i] != 'R' <==> (s[i] == 'L' || s[i] == 'U' || s[i] == 'D')
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" <==> EasilyPlayable(s)
    ensures result in
// </vc-spec>
// <vc-code>
{
  var evenCheck := true;
  var oddCheck := true;
  var i := 0;
  
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant evenCheck == (forall j :: 0 <= j < i && j % 2 == 0 ==> s[j] != 'L')
    invariant oddCheck == (forall j :: 0 <= j < i && j % 2 == 1 ==> s[j] != 'R')
  {
    if i % 2 == 0 {
      evenCheck := evenCheck && s[i] != 'L';
    } else {
      oddCheck := oddCheck && s[i] != 'R';
    }
    i := i + 1;
  }
  
  if evenCheck && oddCheck {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

