// <vc-preamble>
// Helper function to count the number of true values in a boolean sequence
function CountTrue(condition: seq<bool>): nat
{
    if |condition| == 0 then 0
    else (if condition[0] then 1 else 0) + CountTrue(condition[1..])
}

// Helper function to get the i-th true position in the condition array
function GetIthTruePosition(condition: seq<bool>, i: nat): nat
    requires i < CountTrue(condition)
    decreases |condition|
{
    if |condition| == 0 then 0
    else if condition[0] then
        if i == 0 then 0
        else 1 + GetIthTruePosition(condition[1..], i - 1)
    else 1 + GetIthTruePosition(condition[1..], i)
}

// Helper predicate to check if a position is the k-th true position
predicate IsKthTruePosition(condition: seq<bool>, pos: nat, k: nat)
    requires pos < |condition|
    requires k < CountTrue(condition)
{
    GetIthTruePosition(condition, k) == pos
}

/**
 * Extract elements from an array where the corresponding condition is true.
 * Returns a new sequence containing only the elements at positions where 
 * condition is true, preserving their original order.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed CountTrueIncremental assertion and added sequence lemmas */
lemma CountTrueIncremental(condition: seq<bool>, i: nat)
    requires 0 < i <= |condition|
    ensures CountTrue(condition[..i]) == CountTrue(condition[..i-1]) + (if condition[i-1] then 1 else 0)
{
    if i == 1 {
        assert condition[..1] == [condition[0]];
        assert condition[..0] == [];
        assert CountTrue(condition[..1]) == (if condition[0] then 1 else 0);
        assert CountTrue(condition[..0]) == 0;
    } else {
        assert condition[..i] == condition[..i-1] + [condition[i-1]];
        CountTrueSeqConcat(condition[..i-1], [condition[i-1]]);
    }
}

lemma CountTrueSeqConcat(s1: seq<bool>, s2: seq<bool>)
    ensures CountTrue(s1 + s2) == CountTrue(s1) + CountTrue(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        CountTrueSeqConcat(s1[1..], s2);
    }
}

lemma GetIthTruePositionBounds(condition: seq<bool>, i: nat)
    requires i < CountTrue(condition)
    ensures var pos := GetIthTruePosition(condition, i);
            pos < |condition| && condition[pos]
{
    if |condition| == 0 {
        assert false;
    } else if condition[0] {
        if i == 0 {
            assert GetIthTruePosition(condition, 0) == 0;
        } else {
            GetIthTruePositionBounds(condition[1..], i-1);
        }
    } else {
        GetIthTruePositionBounds(condition[1..], i);
    }
}

lemma GetIthTruePositionStrictlyIncreasing(condition: seq<bool>, i: nat, j: nat)
    requires i < j < CountTrue(condition)
    ensures GetIthTruePosition(condition, i) < GetIthTruePosition(condition, j)
{
    if |condition| == 0 {
        assert false;
    } else if condition[0] {
        if i == 0 {
            GetIthTruePositionBounds(condition[1..], j-1);
        } else {
            GetIthTruePositionStrictlyIncreasing(condition[1..], i-1, j-1);
        }
    } else {
        GetIthTruePositionStrictlyIncreasing(condition[1..], i, j);
    }
}

lemma CountTrueMonotonic(condition: seq<bool>, i: nat, j: nat)
    requires 0 <= i <= j <= |condition|
    ensures CountTrue(condition[..i]) <= CountTrue(condition[..j])
{
    if i == j {
        return;
    } else {
        CountTrueMonotonic(condition, i, j-1);
        if j > 0 {
            CountTrueIncremental(condition, j);
        }
    }
}

lemma CountTruePositive(condition: seq<bool>)
    requires |condition| > 0
    requires exists i :: 0 <= i < |condition| && condition[i]
    ensures CountTrue(condition) > 0
{
    if condition[0] {
        assert CountTrue(condition) >= 1;
    } else {
        CountTruePositive(condition[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method Extract(condition: seq<bool>, arr: seq<int>) returns (result: seq<int>)
    requires |condition| == |arr|
    ensures |result| == CountTrue(condition)
    // Each element in result comes from arr at a position where condition is true
    ensures forall k :: 0 <= k < |result| ==> 
        exists i :: 0 <= i < |arr| && condition[i] && result[k] == arr[i]
    // The order is preserved: elements appear in the same relative order as in arr
    ensures forall k1, k2 :: 0 <= k1 < k2 < |result| ==> 
        exists i1, i2 :: (0 <= i1 < i2 < |arr| && 
        condition[i1] && condition[i2] && 
        result[k1] == arr[i1] && result[k2] == arr[i2])
    // Every true position in condition contributes exactly one element to the result
    ensures forall i :: 0 <= i < |arr| && condition[i] ==> 
        exists k :: 0 <= k < |result| && result[k] == arr[i]
    // More precise: the k-th element of result corresponds to the k-th true position in condition
    ensures forall k :: 0 <= k < |result| ==> 
        var pos := GetIthTruePosition(condition, k);
        pos < |arr| && condition[pos] && result[k] == arr[pos]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proper bounds checking for GetIthTruePosition calls */
    result := [];
    var k := 0;
    
    while k < |condition|
        invariant 0 <= k <= |condition|
        invariant |result| == CountTrue(condition[..k])
        invariant forall i :: 0 <= i < |result| ==> 
            var pos := GetIthTruePosition(condition, i);
            pos < k && condition[pos] && result[i] == arr[pos]
        invariant forall i :: 0 <= i < k && condition[i] ==>
            exists j :: 0 <= j < |result| && result[j] == arr[i]
        invariant forall i1, i2 :: 0 <= i1 < i2 < |result| ==>
            var pos1 := GetIthTruePosition(condition, i1);
            var pos2 := GetIthTruePosition(condition, i2);
            pos1 < pos2 && condition[pos1] && condition[pos2] &&
            result[i1] == arr[pos1] && result[i2] == arr[pos2]
    {
        if condition[k] {
            if k+1 <= |condition| {
                CountTrueIncremental(condition, k+1);
            }
            var oldLen := |result|;
            result := result + [arr[k]];
            
            if oldLen > 0 && oldLen < CountTrue(condition) {
                GetIthTruePositionBounds(condition, oldLen);
            }
        } else {
            if k+1 <= |condition| {
                CountTrueIncremental(condition, k+1);
            }
        }
        k := k + 1;
    }
    
    assert condition[..|condition|] == condition;
    
    forall i, j | 0 <= i < j < |result|
        ensures exists i1, i2 :: (0 <= i1 < i2 < |arr| &&
                condition[i1] && condition[i2] &&
                result[i] == arr[i1] && result[j] == arr[i2])
    {
        if i < CountTrue(condition) && j < CountTrue(condition) {
            GetIthTruePositionBounds(condition, i);
            GetIthTruePositionBounds(condition, j);
            GetIthTruePositionStrictlyIncreasing(condition, i, j);
            var pos1 := GetIthTruePosition(condition, i);
            var pos2 := GetIthTruePosition(condition, j);
            assert pos1 < pos2;
        }
    }
}
// </vc-code>
