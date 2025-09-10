predicate ValidInput(skills: seq<int>)
{
    |skills| >= 0
}

predicate HasAdjacentSkills(skills: seq<int>)
{
    exists i, j :: 0 <= i < j < |skills| && (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1)
}

// <vc-helpers>
lemma HasAdjacentSkillsDecidable(skills: seq<int>)
    ensures HasAdjacentSkills(skills) || !HasAdjacentSkills(skills)
{
}

lemma CheckAdjacentPair(skills: seq<int>, i: int, j: int)
    requires 0 <= i < j < |skills|
    ensures (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1) ==> HasAdjacentSkills(skills)
{
}

lemma NoAdjacentInPrefix(skills: seq<int>, i: int)
    requires 0 <= i <= |skills|
    requires forall x, y :: 0 <= x < y < i ==> !(skills[x] - skills[y] == 1 || skills[y] - skills[x] == 1)
    ensures forall x, y :: 0 <= x < y < i ==> !(skills[x] - skills[y] == 1 || skills[y] - skills[x] == 1)
{
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
    var i := 0;
    while i < |skills|
        invariant 0 <= i <= |skills|
        invariant forall x, y :: 0 <= x < y < i ==> !(skills[x] - skills[y] == 1 || skills[y] - skills[x] == 1)
    {
        var j := i + 1;
        while j < |skills|
            invariant i + 1 <= j <= |skills|
            invariant forall y :: i + 1 <= y < j ==> !(skills[i] - skills[y] == 1 || skills[y] - skills[i] == 1)
            invariant forall x, y :: 0 <= x < y < i ==> !(skills[x] - skills[y] == 1 || skills[y] - skills[x] == 1)
        {
            if skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1 {
                CheckAdjacentPair(skills, i, j);
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

