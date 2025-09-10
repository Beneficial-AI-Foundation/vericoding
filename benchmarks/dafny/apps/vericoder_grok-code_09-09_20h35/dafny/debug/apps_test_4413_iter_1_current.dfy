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
  var hasAdjacent := false;
  while i < |skills| 
    invariant 0 <= i <= |skills|
    invariant hasAdjacent == exists k, l :: 0 <= k < l < i && (skills[k] - skills[l] == 1 || skills[l] - skills[k] == 1)
  {
    var j := i + 1;
    while j < |skills|
      invariant i + 1 <= j <= |skills|
      invariant hasAdjacent == (exists k, l :: 0 <= k < l < i && (skills[k] - skills[l] == 1 || skills[l] - skills[k] == 1)) ||
                              (exists k :: 0 <= k < i && (skills[k] - skills[i] == 1 || skills[i] - skills[k] == 1)) ||
                              (exists k :: i < k < j && (skills[i] - skills[k] == 1 || skills[k] - skills[i] == 1))
    {
      if skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1
      {
        hasAdjacent := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  teams := if hasAdjacent then 2 else 1;
}
// </vc-code>

