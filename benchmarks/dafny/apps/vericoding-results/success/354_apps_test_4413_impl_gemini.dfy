predicate ValidInput(skills: seq<int>)
{
    |skills| >= 0
}

predicate HasAdjacentSkills(skills: seq<int>)
{
    exists i, j :: 0 <= i < j < |skills| && (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(skills: seq<int>) returns (teams: int)
    requires ValidInput(skills)
    ensures teams == 1 || teams == 2
    ensures teams == 2 <==> HasAdjacentSkills(skills)
    ensures teams == 1 <==> !HasAdjacentSkills(skills)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |skills|
    invariant 0 <= i <= |skills|
    invariant forall k, l :: 0 <= k < i && k < l < |skills| ==> !(skills[k] - skills[l] == 1 || skills[l] - skills[k] == 1)
  {
    var j := i + 1;
    while j < |skills|
      invariant 0 <= i < |skills|
      invariant i + 1 <= j <= |skills|
      invariant forall k, l :: 0 <= k < i && k < l < |skills| ==> !(skills[k] - skills[l] == 1 || skills[l] - skills[k] == 1)
      invariant forall l :: i < l < j ==> !(skills[i] - skills[l] == 1 || skills[l] - skills[i] == 1)
    {
      if skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1 {
        teams := 2;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  teams := 1;
}
// </vc-code>

