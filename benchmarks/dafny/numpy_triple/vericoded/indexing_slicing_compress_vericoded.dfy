// <vc-preamble>
// Helper function to count true values in a boolean sequence
ghost function CountTrue(condition: seq<bool>): nat
{
    if |condition| == 0 then 0
    else (if condition[0] then 1 else 0) + CountTrue(condition[1..])
}

// Helper predicate to check if a mapping preserves order
ghost predicate IsStrictlyIncreasing(mapping: seq<nat>)
{
    forall i, j :: 0 <= i < j < |mapping| ==> mapping[i] < mapping[j]
}

// Helper predicate to check if all mapped indices have true conditions
ghost predicate MappingRespectsConditions(mapping: seq<nat>, condition: seq<bool>)
    requires forall i :: 0 <= i < |mapping| ==> mapping[i] < |condition|
{
    forall i :: 0 <= i < |mapping| ==> condition[mapping[i]]
}

// Helper predicate to check if result elements match original at mapped positions
ghost predicate ResultMatchesOriginal(result: seq<real>, original: seq<real>, mapping: seq<nat>)
    requires |result| == |mapping|
    requires forall i :: 0 <= i < |mapping| ==> mapping[i] < |original|
{
    forall i :: 0 <= i < |result| ==> result[i] == original[mapping[i]]
}

/**
 * Compresses a vector by selecting only elements where the corresponding condition is true.
 * Returns a new vector containing only the selected elements in their original order.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove CountTrue bounds for slices */
// Helper lemma to count true values bounds
lemma CountTrueBounds(condition: seq<bool>)
    ensures CountTrue(condition) <= |condition|
{
    if |condition| == 0 {
        assert CountTrue(condition) == 0;
    } else {
        CountTrueBounds(condition[1..]);
        assert CountTrue(condition) == (if condition[0] then 1 else 0) + CountTrue(condition[1..]);
        assert CountTrue(condition[1..]) <= |condition[1..]|;
    }
}

// Helper lemma to prove CountTrue increments correctly
lemma CountTrueIncrement(condition: seq<bool>, i: int)
    requires 0 <= i < |condition|
    ensures CountTrue(condition[..i+1]) == CountTrue(condition[..i]) + (if condition[i] then 1 else 0)
{
    if i == 0 {
        assert condition[..1] == [condition[0]];
        assert CountTrue(condition[..0]) == 0;
    } else {
        var prefix := condition[..i];
        var fullPrefix := condition[..i+1];
        assert fullPrefix == prefix + [condition[i]];
        CountTrueAddElement(prefix, condition[i]);
    }
}

// Helper lemma for adding one element to CountTrue
lemma CountTrueAddElement(s: seq<bool>, b: bool)
    ensures CountTrue(s + [b]) == CountTrue(s) + (if b then 1 else 0)
{
    if |s| == 0 {
        assert s + [b] == [b];
    } else {
        assert s + [b] == [s[0]] + (s[1..] + [b]);
        CountTrueAddElement(s[1..], b);
    }
}

// Helper lemma to prove IsStrictlyIncreasing is maintained
lemma MaintainStrictlyIncreasing(mapping: seq<nat>, newIndex: nat)
    requires IsStrictlyIncreasing(mapping)
    requires forall i :: 0 <= i < |mapping| ==> mapping[i] < newIndex
    ensures IsStrictlyIncreasing(mapping + [newIndex])
{
    var newMapping := mapping + [newIndex];
    forall i, j | 0 <= i < j < |newMapping|
        ensures newMapping[i] < newMapping[j]
    {
        if j == |mapping| {
            assert newMapping[j] == newIndex;
            assert newMapping[i] == mapping[i];
            assert mapping[i] < newIndex;
        } else {
            assert newMapping[i] == mapping[i];
            assert newMapping[j] == mapping[j];
            assert mapping[i] < mapping[j];
        }
    }
}

// Helper lemma to prove empty condition implies CountTrue is 0
lemma EmptyConditionImpliesZeroCount(condition: seq<bool>)
    requires forall i :: 0 <= i < |condition| ==> !condition[i]
    ensures CountTrue(condition) == 0
{
    if |condition| == 0 {
        assert CountTrue(condition) == 0;
    } else {
        assert !condition[0];
        EmptyConditionImpliesZeroCount(condition[1..]);
    }
}

// Helper lemma to prove full condition implies CountTrue equals length
lemma FullConditionImpliesFullCount(condition: seq<bool>)
    requires forall i :: 0 <= i < |condition| ==> condition[i]
    ensures CountTrue(condition) == |condition|
{
    if |condition| == 0 {
        assert CountTrue(condition) == 0;
    } else {
        assert condition[0];
        FullConditionImpliesFullCount(condition[1..]);
    }
}

// Helper lemma to prove contradiction when CountTrue is 0 but some element is true
lemma CountTrueZeroContradiction(condition: seq<bool>, j: int)
    requires 0 <= j < |condition|
    requires condition[j]
    ensures CountTrue(condition) > 0
{
    if j == 0 {
        assert CountTrue(condition) == 1 + CountTrue(condition[1..]);
    } else {
        CountTrueZeroContradiction(condition[1..], j-1);
        assert CountTrue(condition) == (if condition[0] then 1 else 0) + CountTrue(condition[1..]);
    }
}

// Helper lemma to prove contradiction when CountTrue equals length but some element is false
lemma CountTrueFullContradiction(condition: seq<bool>, j: int)
    requires 0 <= j < |condition|
    requires !condition[j]
    ensures CountTrue(condition) < |condition|
{
    if j == 0 {
        assert CountTrue(condition) == 0 + CountTrue(condition[1..]);
        CountTrueBounds(condition[1..]);
        assert CountTrue(condition[1..]) <= |condition[1..]|;
    } else {
        CountTrueFullContradiction(condition[1..], j-1);
        assert CountTrue(condition) == (if condition[0] then 1 else 0) + CountTrue(condition[1..]);
        assert CountTrue(condition[1..]) < |condition[1..]|;
    }
}
// </vc-helpers>

// <vc-spec>
method Compress(condition: seq<bool>, a: seq<real>) returns (result: seq<real>)
    requires |condition| == |a|
    ensures |result| == CountTrue(condition)
    // Result preserves order and corresponds to true conditions via a mapping
    ensures exists mapping: seq<nat> ::
        && |mapping| == |result|
        && (forall i :: 0 <= i < |mapping| ==> mapping[i] < |condition|)
        && MappingRespectsConditions(mapping, condition)
        && ResultMatchesOriginal(result, a, mapping)
        && IsStrictlyIncreasing(mapping)
    // Empty result iff all conditions are false
    ensures (|result| == 0) <==> (forall i :: 0 <= i < |condition| ==> !condition[i])
    // Full result iff all conditions are true
    ensures (|result| == |a|) <==> (forall i :: 0 <= i < |condition| ==> condition[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added bounds lemma assertion to help verify slice bounds */
    result := [];
    ghost var mapping: seq<nat> := [];
    var i := 0;
    
    while i < |condition|
        invariant 0 <= i <= |condition|
        invariant |result| == CountTrue(condition[..i])
        invariant |mapping| == |result|
        invariant forall j :: 0 <= j < |mapping| ==> 0 <= mapping[j] < |condition| && mapping[j] < i && condition[mapping[j]]
        invariant IsStrictlyIncreasing(mapping)
        invariant forall j :: 0 <= j < |result| ==> j < |mapping| && mapping[j] < |a| && result[j] == a[mapping[j]]
    {
        CountTrueIncrement(condition, i);
        
        if condition[i] {
            result := result + [a[i]];
            MaintainStrictlyIncreasing(mapping, i as nat);
            mapping := mapping + [i as nat];
        }
        
        i := i + 1;
        CountTrueBounds(condition[1..]);
    }
    
    assert condition[..i] == condition;
    assert |result| == CountTrue(condition);
    
    // Verify empty result condition
    if |result| == 0 {
        assert CountTrue(condition) == 0;
        forall j | 0 <= j < |condition|
            ensures !condition[j]
        {
            if condition[j] {
                CountTrueZeroContradiction(condition, j);
                assert CountTrue(condition) > 0;
                assert false;
            }
        }
    }
    if forall j :: 0 <= j < |condition| ==> !condition[j] {
        EmptyConditionImpliesZeroCount(condition);
        assert |result| == 0;
    }
    
    // Verify full result condition
    if |result| == |a| {
        assert CountTrue(condition) == |condition|;
        forall j | 0 <= j < |condition|
            ensures condition[j]
        {
            if !condition[j] {
                CountTrueFullContradiction(condition, j);
                assert CountTrue(condition) < |condition|;
                assert false;
            }
        }
    }
    if forall j :: 0 <= j < |condition| ==> condition[j] {
        FullConditionImpliesFullCount(condition);
        assert |result| == |a|;
    }
    
    // Final assertions for postcondition
    assert |mapping| == |result|;
    assert forall j :: 0 <= j < |mapping| ==> mapping[j] < |condition|;
    assert MappingRespectsConditions(mapping, condition);
    assert ResultMatchesOriginal(result, a, mapping);
    assert IsStrictlyIncreasing(mapping);
}
// </vc-code>
