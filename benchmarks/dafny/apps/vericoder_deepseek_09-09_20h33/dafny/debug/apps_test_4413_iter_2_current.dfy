predicate ValidInput(skills: seq<int>)
{
    |skills| >= 0
}

predicate HasAdjacentSkills(skills: seq<int>)
{
    exists i, j :: 0 <= i < j < |skills| && (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1)
}

// <vc-helpers>
lemma AdjacentExists(s1: int, s2: int)
    ensures (s1 - s2 == 1 || s2 - s1 == 1) ==
            (exists i, j :: 0 <= i < j < 2 && 
                ([s1, s2][i] - [s1, s2][j] == 1 || [s1, s2][j] - [s1, s2][i] == 1))
{
    if s1 - s2 == 1 || s2 - s1 == 1 {
        // The indices 0 and 1 satisfy the condition
    } else {
        // No adjacent pair exists
    }
}

lemma AdjacentExistsSeq(s: seq<int>)
    requires |s| > 1
    ensures HasAdjacentSkills(s) == 
            (exists i :: 0 <= i < |s| - 1 && (s[i] - s[i+1] == 1 || s[i+1] - s[i] == 1))
{
    if HasAdjacentSkills(s) {
        var i, j :| 0 <= i < j < |s| && (s[i] - s[j] == 1 || s[j] - s[i] == 1);
        // Show that there must be consecutive adjacent elements
        // by considering the minimal distance between i and j
        if j == i + 1 {
            // Already consecutive
        } else {
            // Check all elements between i and j to find consecutive adjacent pair
            var k := i;
            while k < j
                invariant i <= k <= j
                invariant exists m,n :: i <= m < n <= j && (s[m] - s[n] == 1 || s[n] - s[m] == 1)
            {
                if s[k] - s[k+1] == 1 || s[k+1] - s[k] == 1 {
                    break;
                }
                k := k + 1;
            }
        }
    }
}

lemma AdjacentForAll(s: seq<int>, n: int)
    requires 0 <= n <= |s| - 1
    requires forall j :: 0 <= j < n ==> (skills[j] - skills[j+1] != 1 && skills[j+1] - skills[j] != 1)
    ensures !HasAdjacentSkills(s[0..n+1])
{
}

lemma FoundAdjacentImpliesHasAdjacent(s: seq<int>, j: int)
    requires 0 <= j < |s| - 1
    requires s[j] - s[j+1] == 1 || s[j+1] - s[j] == 1
    ensures HasAdjacentSkills(s)
{
    assert 0 <= j < j+1 < |s|;
}
// </vc-helpers>
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
    if |skills| == 0 || |skills| == 1 {
        teams := 1;
        assert !HasAdjacentSkills(skills);
    } else {
        var foundAdjacent := false;
        var i := 0;
        while i < |skills| - 1
            invariant 0 <= i <= |skills| - 1
            invariant !foundAdjacent ==> forall j :: 0 <= j < i ==> (skills[j] - skills[j+1] != 1 && skills[j+1] - skills[j] != 1)
            invariant foundAdjacent ==> exists j :: 0 <= j < i && (skills[j] - skills[j+1] == 1 || skills[j+1] - skills[j] == 1)
            invariant !foundAdjacent ==> !HasAdjacentSkills(skills[0..i+1])
        {
            if skills[i] - skills[i+1] == 1 || skills[i+1] - skills[i] == 1 {
                foundAdjacent := true;
                assert HasAdjacentSkills(skills);
            } else {
                if !foundAdjacent {
                    AdjacentForAll(skills, i);
                }
            }
            i := i + 1;
        }
        
        if foundAdjacent {
            teams := 2;
            assert HasAdjacentSkills(skills);
        } else {
            teams := 1;
            // Proof that no adjacent skills exist in the entire sequence
            if HasAdjacentSkills(skills) {
                var j, k :| 0 <= j < k < |skills| && (skills[j] - skills[k] == 1 || skills[k] - skills[j] == 1);
                // Since j and k are not consecutive, we need to show there must be consecutive adjacent elements
                var max_index := if j > k then j else k;
                var min_index := if j < k then j else k;
                var temp := min_index;
                while temp < max_index
                    invariant min_index <= temp <= max_index
                {
                    if skills[temp] - skills[temp+1] == 1 || skills[temp+1] - skills[temp] == 1 {
                        assert false; // Contradiction with our invariant
                    }
                    temp := temp + 1;
                }
                assert false; // This shouldn't be reachable
            }
        }
    }
}
// </vc-code>

