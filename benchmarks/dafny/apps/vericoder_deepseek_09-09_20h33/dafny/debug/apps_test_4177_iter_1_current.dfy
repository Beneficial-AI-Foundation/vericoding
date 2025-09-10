predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(s: string, result: string)
{
    |result| == |s| && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>
lemma StringLength(s: string)
  ensures |s| >= 0

lemma CharacterAccess(s: string, i: int)
  requires 0 <= i < |s|
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
  result := new string[s.Length];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == |s|
    invariant forall j :: 0 <= j < i ==> result[j] == 'x'
  {
    result := result[0..i] + ['x'] + result[i+1..];
    i := i + 1;
  }
}
// </vc-code>

