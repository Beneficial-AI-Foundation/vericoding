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

lemma NoAdjacentSkillsInSmallSequence(skills: seq<int>)
    requires |skills| <= 1
    ensures !HasAdjacentSkills(skills)
{
    // For sequences of length 0 or 1, there can't be two distinct indices i < j
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
        NoAdjacentSkillsInSmallSequence(skills);
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
            invariant i + 1 <= j <= |skills|
            invariant !found ==> forall q :: i + 1 <= q < j ==> skills[i] - skills[q] != 1 && skills[q] - skills[i] != 1
            invariant !found ==> forall p, q :: 0 <= p < q < i ==> skills[p] - skills[q] != 1 && skills[q] - skills[p] != 1
            invariant found ==> HasAdjacentSkills(skills)
        {
            if skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1 {
                found := true;
                HasAdjacentSkillsImplication(skills, i, j);
            }
            j := j + 1;
        }
        
        if !found && j == |skills| {
            // After checking all j > i, we know there's no adjacent skill with index i
            assert forall q :: i < q < |skills| ==> skills[i] - skills[q] != 1 && skills[q] - skills[i] != 1;
        }
        
        i := i + 1;
    }
    
    if found {
        teams := 2;
    } else {
        assert i == |skills|;
        assert forall p, q :: 0 <= p < q < |skills| ==> skills[p] - skills[q] != 1 && skills[q] - skills[p] != 1;
        NoAdjacentSkillsFound(skills);
        teams := 1;
    }
}
// </vc-code>

