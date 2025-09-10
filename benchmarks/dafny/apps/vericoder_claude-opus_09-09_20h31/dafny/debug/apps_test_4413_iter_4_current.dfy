predicate ValidInput(skills: seq<int>)
{
    |skills| >= 0
}

predicate HasAdjacentSkills(skills: seq<int>)
{
    exists i, j :: 0 <= i < j < |skills| && (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1)
}

// <vc-helpers>
lemma HasAdjacentSkillsImplication(skills: seq<int>, i: int, j: int)
    requires 0 <= i < j < |skills|
    requires skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1
    ensures HasAdjacentSkills(skills)
{
    // This lemma proves that if we find a pair with difference 1, HasAdjacentSkills is true
}

lemma NoAdjacentSkillsFound(skills: seq<int>)
    requires forall i, j :: 0 <= i < j < |skills| ==> skills[i] - skills[j] != 1 && skills[j] - skills[i] != 1
    ensures !HasAdjacentSkills(skills)
{
    // This proves that if no pair has difference 1, HasAdjacentSkills is false
}

lemma InvariantPreservation(skills: seq<int>, i: int)
    requires 0 <= i < |skills|
    requires forall p, q :: 0 <= p < q < i ==> skills[p] - skills[q] != 1 && skills[q] - skills[p] != 1
    requires forall q :: i < q < |skills| ==> skills[i] - skills[q] != 1 && skills[q] - skills[i] != 1
    ensures forall p, q :: 0 <= p < q < i + 1 ==> skills[p] - skills[q] != 1 && skills[q] - skills[p] != 1
{
    // This lemma helps prove that the invariant is maintained when i is incremented
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
    if |skills| <= 1 {
        teams := 1;
        return;
    }
    
    var found := false;
    var i := 0;
    
    while i < |skills| && !found
        invariant 0 <= i <= |skills|
        invariant !found ==> forall p, q :: 0 <= p < q < i ==> skills[p] - skills[q] != 1 && skills[q] - skills[p] != 1
        invariant found ==> HasAdjacentSkills(skills)
    {
        var j := i + 1;
        while j < |skills| && !found
            invariant i < j <= |skills|
            invariant !found ==> forall q :: i < q < j ==> skills[i] - skills[q] != 1 && skills[q] - skills[i] != 1
            invariant !found ==> forall p, q :: 0 <= p < q < i ==> skills[p] - skills[q] != 1 && skills[q] - skills[p] != 1
            invariant found ==> HasAdjacentSkills(skills)
        {
            if skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1 {
                found := true;
                HasAdjacentSkillsImplication(skills, i, j);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    if found {
        teams := 2;
    } else {
        NoAdjacentSkillsFound(skills);
        teams := 1;
    }
}
// </vc-code>

