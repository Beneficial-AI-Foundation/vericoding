predicate IsEvenString(s: string)
{
    |s| >= 2 && |s| % 2 == 0 && s[..|s|/2] == s[|s|/2..]
}

predicate ValidInput(S: string)
{
    |S| >= 2 && IsEvenString(S)
}

predicate ValidSolution(S: string, result: int)
{
    2 <= result < |S| && result % 2 == 0 && IsEvenString(S[..result])
}

predicate IsMaximalSolution(S: string, result: int)
{
    ValidSolution(S, result) && 
    forall k :: result < k < |S| && k % 2 == 0 ==> !IsEvenString(S[..k])
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    requires exists k :: ValidSolution(S, k)
    ensures ValidSolution(S, result)
    ensures IsMaximalSolution(S, result)
// </vc-spec>
// <vc-code>
{
  ghost var checked: set<int> := {};
  var k := |S| - 2;
  while k >= 2
    invariant 0 <= k < |S|
    invariant k % 2 == 0
    invariant forall j :: j in checked ==> 2 <= j < |S| && j % 2 == 0 && !IsEvenString(S[..j])
    invariant forall j :: k < j < |S| && j % 2 == 0 ==> j in checked
    decreases k / 2
  {
    if IsEvenString(S[..k]) {
      assert forall j :: k < j < |S| && j % 2 == 0 ==> !IsEvenString(S[..j]);
      return k;
    } else {
      assert !IsEvenString(S[..k]);
      assert 2 <= k < |S|;
      assert k % 2 == 0;
      checked := checked + {k};
      k := k - 2;
    }
  }
  // unreachable because precondition guarantees a solution exists
  assert exists k0 :: ValidSolution(S, k0);
  assert false;
}
// </vc-code>

