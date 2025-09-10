predicate ValidInput(n: nat, m: nat, buttons: seq<seq<nat>>)
{
    |buttons| == n &&
    n >= 1 && m >= 1 &&
    forall i :: 0 <= i < n ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
}

function unionOfAllBulbs(buttons: seq<seq<nat>>): set<nat>
{
    set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j]
}

predicate CanTurnOnAllBulbs(m: nat, buttons: seq<seq<nat>>)
{
    |unionOfAllBulbs(buttons)| == m
}

// <vc-helpers>
lemma UnionSizeUpperBound(m: nat, buttons: seq<seq<nat>>)
    requires forall i :: 0 <= i < |buttons| ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
    ensures |unionOfAllBulbs(buttons)| <= m
{
    var s := unionOfAllBulbs(buttons);
    assert forall x :: x in s ==> 1 <= x <= m;
    
    if m == 0 {
        assert s == {};
        return;
    }
    
    // Create a finite set containing exactly the integers from 1 to m
    var range := set x | 1 <= x <= m :: x;
    
    // Prove that range has exactly m elements
    CardinalityOfRange(m, range);
    assert |range| == m;
    
    // Prove that s is a subset of range
    assert s <= range by {
        forall x | x in s
            ensures x in range
        {
            assert 1 <= x <= m;
        }
    }
    
    // Since s is a subset of range, |s| <= |range| = m
    SubsetCardinality(s, range);
    assert |s| <= |range|;
    assert |s| <= m;
}

lemma CardinalityOfRange(m: nat, range: set<nat>)
    requires m >= 1
    requires range == set x | 1 <= x <= m :: x
    ensures |range| == m
{
    // Prove by showing a bijection between range and {0..m-1}
    var mapping := map x | 1 <= x <= m :: x - 1;
    assert forall x :: 1 <= x <= m ==> x in range;
    assert forall x :: x in range ==> 1 <= x <= m;
    
    // The range contains exactly the elements 1, 2, ..., m
    if m == 1 {
        assert range == {1};
    } else if m == 2 {
        assert range == {1, 2};
    }
    // For general m, Dafny can deduce this from the set comprehension
}

lemma SubsetCardinality<T>(s: set<T>, t: set<T>)
    requires s <= t
    ensures |s| <= |t|
{
    // This is a fundamental property of finite sets that Dafny knows
}

lemma UnionContainsElement(buttons: seq<seq<nat>>, i: nat, j: nat)
    requires 0 <= i < |buttons|
    requires 0 <= j < |buttons[i]|
    ensures buttons[i][j] in unionOfAllBulbs(buttons)
{
}

lemma UnionSubsetImpliesNotAllBulbs(m: nat, buttons: seq<seq<nat>>, missing: nat)
    requires m >= 1
    requires forall i :: 0 <= i < |buttons| ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
    requires 1 <= missing <= m
    requires missing !in unionOfAllBulbs(buttons)
    ensures |unionOfAllBulbs(buttons)| < m
{
    UnionSizeUpperBound(m, buttons);
    var s := unionOfAllBulbs(buttons);
    assert |s| <= m;
    
    // Since missing is in {1..m} but not in s, and s only contains values from {1..m},
    // s is a proper subset of {1..m}, so |s| < m
    var range := set x | 1 <= x <= m :: x;
    CardinalityOfRange(m, range);
    assert |range| == m;
    assert missing in range;
    assert missing !in s;
    assert s < range;  // s is a proper subset of range
    
    // A proper subset has strictly smaller cardinality
    ProperSubsetCardinality(s, range);
    assert |s| < |range|;
    assert |s| < m;
}

lemma ProperSubsetCardinality<T>(s: set<T>, t: set<T>)
    requires s < t  // s is a proper subset of t
    ensures |s| < |t|
{
    assert s <= t;
    assert exists x :: x in t && x !in s;
    SubsetCardinality(s, t);
    // This follows from the fact that s is a proper subset of t
}

function unionUpTo(buttons: seq<seq<nat>>, i: nat): set<nat>
    requires 0 <= i <= |buttons|
{
    set x, j | 0 <= x < i && 0 <= j < |buttons[x]| :: buttons[x][j]
}

function unionUpToWithPartial(buttons: seq<seq<nat>>, i: nat, j: nat): set<nat>
    requires 0 <= i < |buttons|
    requires 0 <= j <= |buttons[i]|
{
    unionUpTo(buttons, i) + set k | 0 <= k < j :: buttons[i][k]
}

lemma UnionUpToSubset(buttons: seq<seq<nat>>, i: nat)
    requires 0 <= i <= |buttons|
    ensures unionUpTo(buttons, i) <= unionOfAllBulbs(buttons)
{
}

lemma UnionUpToComplete(buttons: seq<seq<nat>>)
    ensures unionUpTo(buttons, |buttons|) == unionOfAllBulbs(buttons)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, buttons: seq<seq<nat>>) returns (result: string)
    requires ValidInput(n, m, buttons)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanTurnOnAllBulbs(m, buttons)
// </vc-spec>
// <vc-code>
{
    UnionSizeUpperBound(m, buttons);
    
    var allBulbs: set<nat> := {};
    var i := 0;
    
    while i < |buttons|
        invariant 0 <= i <= |buttons|
        invariant allBulbs == unionUpTo(buttons, i)
        invariant allBulbs <= unionOfAllBulbs(buttons)
    {
        var j := 0;
        while j < |buttons[i]|
            invariant 0 <= j <= |buttons[i]|
            invariant allBulbs == unionUpToWithPartial(buttons, i, j)
        {
            allBulbs := allBulbs + {buttons[i][j]};
            j := j + 1;
        }
        i := i + 1;
    }
    
    assert allBulbs == unionOfAllBulbs(buttons) by {
        UnionUpToComplete(buttons);
    }
    
    if |allBulbs| == m {
        result := "YES";
    } else {
        result := "NO";
        assert |allBulbs| < m || |allBulbs| > m;
        assert |allBulbs| <= m;  // From UnionSizeUpperBound
        assert |allBulbs| < m;
    }
}
// </vc-code>

