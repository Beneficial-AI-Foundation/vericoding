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
}

lemma AdjacentExistsSeq(s: seq<int>)
    requires |s| > 1
    ensures HasAdjacentSkills(s) == 
            (exists i :: 0 <= i < |s| - 1 && (s[i] - s[i+1] == 1 || s[i+1] - s[i] == 1))
{
}

lemma AdjacentForAll(s: seq<int>, n: int)
    requires 0 <= n < |s|
    requires forall j :: 0 <= j < n ==> (s[j] - s[j+1] != 1 && s[j+1] - s[j] != 1)
    ensures !HasAdjacentSkills(s[0..n+1])
{
    if n+1 >= 2 {
        AdjacentExistsSeq(s[0..n+1]);
        var k := 0;
        while k < n
            invariant 0 <= k <= n
            invariant forall m :: 0 <= m < k ==> !HasAdjacentSkills(s[0..m+2])
        {
            assert s[k] - s[k+1] != 1 && s[k+1] - s[k] != 1;
            k := k + 1;
        }
    }
}

lemma FoundAdjacentImpliesHasAdjacent(s: seq<int>, j: int)
    requires 0 <= j < |s| - 1
    requires s[j] - s[j+1] == 1 || s[j+1] - s[j] == 1
    ensures HasAdjacentSkills(s)
{
    AdjacentExistsSeq(s);
    assert exists i :: 0 <= i < |s| - 1 && (s[i] - s[i+1] == 1 || s[i+1] - s[i] == 1);
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
    if |skills| == 0 || |skills| == 1 {
        teams := 1;
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
                FoundAdjacentImpliesHasAdjacent(skills, i);
            } else if !foundAdjacent {
                AdjacentForAll(skills, i);
            }
            i := i + 1;
        }
        
        if foundAdjacent {
            teams := 2;
        } else {
            teams := 1;
            AdjacentForAll(skills, |skills| - 1);
        }
    }
}
// </vc-code>

