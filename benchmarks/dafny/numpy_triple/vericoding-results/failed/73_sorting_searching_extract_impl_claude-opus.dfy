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
/* helper modified by LLM (iteration 4): Fixed CountTrueProperties to correctly handle slice relationships */
lemma CountTrueProperties(condition: seq<bool>, i: nat)
    requires i < |condition|
    ensures condition[i] ==> CountTrue(condition[..i+1]) == CountTrue(condition[..i]) + 1
    ensures !condition[i] ==> CountTrue(condition[..i+1]) == CountTrue(condition[..i])
{
    if i == 0 {
        assert condition[..1] == [condition[0]];
        assert condition[..0] == [];
    } else {
        assert condition[..i+1] == condition[..i] + [condition[i]];
        CountTrueSliceAppend(condition[..i], condition[i]);
    }
}

/* helper modified by LLM (iteration 4): Added helper lemma for counting in slice plus one element */
lemma CountTrueSliceAppend(s: seq<bool>, b: bool)
    ensures CountTrue(s + [b]) == CountTrue(s) + (if b then 1 else 0)
{
    if |s| == 0 {
        assert s + [b] == [b];
    } else {
        assert (s + [b])[0] == s[0];
        assert (s + [b])[1..] == s[1..] + [b];
        CountTrueSliceAppend(s[1..], b);
    }
}

lemma GetIthTruePositionBounds(condition: seq<bool>, i: nat)
    requires i < CountTrue(condition)
    ensures GetIthTruePosition(condition, i) < |condition|
    ensures condition[GetIthTruePosition(condition, i)]
    decreases |condition|
{
    if |condition| == 0 {
    } else if condition[0] {
        if i == 0 {
        } else {
            GetIthTruePositionBounds(condition[1..], i - 1);
        }
    } else {
        GetIthTruePositionBounds(condition[1..], i);
    }
}

lemma GetIthTruePositionOrdering(condition: seq<bool>, i: nat, j: nat)
    requires i < j < CountTrue(condition)
    ensures GetIthTruePosition(condition, i) < GetIthTruePosition(condition, j)
    decreases |condition|
{
    if |condition| == 0 {
    } else if condition[0] {
        if i == 0 {
            GetIthTruePositionBounds(condition[1..], j - 1);
        } else {
            GetIthTruePositionOrdering(condition[1..], i - 1, j - 1);
        }
    } else {
        GetIthTruePositionOrdering(condition[1..], i, j);
    }
}

/* helper modified by LLM (iteration 4): Added lemma to connect true positions with result indices */
lemma TruePositionToIndex(condition: seq<bool>, pos: nat)
    requires pos < |condition|
    requires condition[pos]
    ensures exists k :: 0 <= k < CountTrue(condition) && GetIthTruePosition(condition, k) == pos
    decreases |condition|, pos
{
    if pos == 0 {
        assert GetIthTruePosition(condition, 0) == 0;
    } else if condition[0] {
        TruePositionToIndex(condition[1..], pos - 1);
        var k :| 0 <= k < CountTrue(condition[1..]) && GetIthTruePosition(condition[1..], k) == pos - 1;
        assert GetIthTruePosition(condition, k + 1) == pos;
    } else {
        TruePositionToIndex(condition[1..], pos - 1);
        var k :| 0 <= k < CountTrue(condition[1..]) && GetIthTruePosition(condition[1..], k) == pos - 1;
        assert GetIthTruePosition(condition, k) == pos;
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
/* code modified by LLM (iteration 4): Added proper invariants to establish all postconditions */
{
    result := [];
    var count := CountTrue(condition);
    var k := 0;
    
    while k < count
        invariant 0 <= k <= count
        invariant |result| == k
        invariant forall m :: 0 <= m < k ==> 
            var pos := GetIthTruePosition(condition, m);
            pos < |arr| && condition[pos] && result[m] == arr[pos]
        invariant forall m :: 0 <= m < k ==> 
            exists i :: 0 <= i < |arr| && condition[i] && result[m] == arr[i]
        invariant forall m1, m2 :: 0 <= m1 < m2 < k ==> 
            var pos1 := GetIthTruePosition(condition, m1);
            var pos2 := GetIthTruePosition(condition, m2);
            0 <= pos1 < pos2 < |arr| && 
            condition[pos1] && condition[pos2] && 
            result[m1] == arr[pos1] && result[m2] == arr[pos2]
        invariant forall i :: 0 <= i < |arr| && condition[i] && 
            (exists m :: 0 <= m < k && GetIthTruePosition(condition, m) == i) ==>
            exists m :: 0 <= m < k && result[m] == arr[i]
    {
        var pos := GetIthTruePosition(condition, k);
        GetIthTruePositionBounds(condition, k);
        
        // Prove ordering for all previous elements
        forall m1, m2 | 0 <= m1 < m2 <= k
            ensures m2 == k ==> GetIthTruePosition(condition, m1) < GetIthTruePosition(condition, m2)
        {
            if m2 == k && m1 < k {
                GetIthTruePositionOrdering(condition, m1, k);
            }
        }
        
        result := result + [arr[pos]];
        k := k + 1;
    }
    
    // Establish the remaining postcondition
    forall i | 0 <= i < |arr| && condition[i]
        ensures exists m :: 0 <= m < |result| && result[m] == arr[i]
    {
        TruePositionToIndex(condition, i);
        var m :| 0 <= m < CountTrue(condition) && GetIthTruePosition(condition, m) == i;
        assert result[m] == arr[i];
    }
}
// </vc-code>
