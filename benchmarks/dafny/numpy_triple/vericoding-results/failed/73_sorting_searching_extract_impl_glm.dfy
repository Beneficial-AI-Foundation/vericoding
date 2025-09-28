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
/* helper modified by LLM (iteration 2): replaced calc blocks with explicit equality proofs */
lemma GetIthTruePositionIsStrictlyIncreasing(condition: seq<bool>, k1: nat, k2: nat)
    requires k1 < k2 < CountTrue(condition)
    ensures GetIthTruePosition(condition, k1) < GetIthTruePosition(condition, k2)
{
    if |condition| == 0 {
        assert false; // impossible by precondition
    } else {
        if condition[0] {
            if k1 == 0 {
                assert GetIthTruePosition(condition, k1) == 0;
                assert GetIthTruePosition(condition, k2) == 1 + GetIthTruePosition(condition[1..], k2-1);
                assert 0 < 1 + GetIthTruePosition(condition[1..], k2-1);
            } else {
                GetIthTruePositionIsStrictlyIncreasing(condition[1..], k1-1, k2-1);
                assert GetIthTruePosition(condition, k1) == 1 + GetIthTruePosition(condition[1..], k1-1);
                assert GetIthTruePosition(condition, k2) == 1 + GetIthTruePosition(condition[1..], k2-1);
                assert GetIthTruePosition(condition[1..], k1-1) < GetIthTruePosition(condition[1..], k2-1);
                assert 1 + GetIthTruePosition(condition[1..], k1-1) < 1 + GetIthTruePosition(condition[1..], k2-1);
            }
        } else {
            GetIthTruePositionIsStrictlyIncreasing(condition[1..], k1, k2);
            assert GetIthTruePosition(condition, k1) == 1 + GetIthTruePosition(condition[1..], k1);
            assert GetIthTruePosition(condition, k2) == 1 + GetIthTruePosition(condition[1..], k2);
            assert GetIthTruePosition(condition[1..], k1) < GetIthTruePosition(condition[1..], k2);
            assert 1 + GetIthTruePosition(condition[1..], k1) < 1 + GetIthTruePosition(condition[1..], k2);
        }
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
  /* code modified by LLM (iteration 2): fixed sequence construction using concatenation */
  var n := CountTrue(condition);
  result := [];
  
  for k := 0 to n
      invariant |result| == k
      invariant forall i :: 0 <= i < k ==> 
          var pos := GetIthTruePosition(condition, i);
          pos < |arr| && condition[pos] && result[i] == arr[pos]
  {
      if k < n {
          var pos := GetIthTruePosition(condition, k);
          result := result + [arr[pos]];
      }
  }
}
// </vc-code>
