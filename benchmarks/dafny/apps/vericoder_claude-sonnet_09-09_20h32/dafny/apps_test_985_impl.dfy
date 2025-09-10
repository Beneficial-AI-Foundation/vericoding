predicate ValidInput(positions: seq<(int, int)>)
{
    |positions| >= 1 && |positions| <= 200000 &&
    (forall i :: 0 <= i < |positions| ==> 
        1 <= positions[i].0 <= 1000 && 1 <= positions[i].1 <= 1000) &&
    (forall i, j :: 0 <= i < j < |positions| ==> positions[i] != positions[j])
}

function CountAttackingPairs(positions: seq<(int, int)>): int
    requires ValidInput(positions)
{
    |set i, j | 0 <= i < j < |positions| && 
               (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
                positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i, j)|
}

predicate ValidOutput(positions: seq<(int, int)>, result: int)
    requires ValidInput(positions)
{
    result == CountAttackingPairs(positions) && result >= 0
}

// <vc-helpers>
lemma CountAttackingPairsNonNegative(positions: seq<(int, int)>)
    requires ValidInput(positions)
    ensures CountAttackingPairs(positions) >= 0
{
    // The cardinality of any set is non-negative
}

lemma AttackingPairsEquivalence(positions: seq<(int, int)>, pairs: set<(int, int)>)
    requires ValidInput(positions)
    requires pairs == set i, j | 0 <= i < j < |positions| && 
                     (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
                      positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i, j)
    ensures |pairs| == CountAttackingPairs(positions)
{
    // Direct from definition
}
// </vc-helpers>

// <vc-spec>
method SolveBishops(positions: seq<(int, int)>) returns (result: int)
    requires ValidInput(positions)
    ensures ValidOutput(positions, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var pairs := set i, j | 0 <= i < j < |positions| && 
                           (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
                            positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i, j);
    
    result := |pairs|;
    
    CountAttackingPairsNonNegative(positions);
    AttackingPairsEquivalence(positions, pairs);
}
// </vc-code>

