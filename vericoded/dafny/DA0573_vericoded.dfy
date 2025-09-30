predicate ValidInput(skills: seq<int>)
{
    |skills| >= 0
}

predicate HasAdjacentSkills(skills: seq<int>)
{
    exists i, j :: 0 <= i < j < |skills| && (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1)
}

// <vc-helpers>
predicate Adj(x:int, y:int)
{
  x - y == 1 || y - x == 1
}
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
  var n := |skills|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall a,b :: 0 <= a < b < i ==> !(skills[a] - skills[b] == 1 || skills[b] - skills[a] == 1)
    invariant forall a :: 0 <= a < i ==> forall b :: a < b < n ==> !(skills[a] - skills[b] == 1 || skills[b] - skills[a] == 1)
  {
    var j := i + 1;
    while j < n
      invariant i+1 <= j <= n
      invariant 0 <= i < n
      invariant forall a :: 0 <= a < i ==> forall b :: a < b < n ==> !(skills[a] - skills[b] == 1 || skills[b] - skills[a] == 1)
      invariant forall b :: i < b < j ==> !(skills[i] - skills[b] == 1 || skills[b] - skills[i] == 1)
    {
      if skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1 {
        return 2;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return 1;
}
// </vc-code>

