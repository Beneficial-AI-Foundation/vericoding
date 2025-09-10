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
{
}

lemma CharacterAccess(s: string, i: int)
  requires 0 <= i < |s|
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  result := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == n
    invariant forall j :: 0 <= j < i ==> result[j] == 'x'
  {
    result[i] := 'x';
    i := i + 1;
  }
  result := new string(result);
}
// </vc-code>

