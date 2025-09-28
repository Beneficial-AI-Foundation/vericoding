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
/* helper modified by LLM (iteration 5): Added complete proof for CountTrueLemma with proper slicing */
lemma CountTrueLemma(condition: seq<bool>, i: int)
  requires 0 <= i <= |condition|
  ensures CountTrue(condition) == CountTrue(condition[..i]) + CountTrue(condition[i..])
{
  if i == 0 {
    // Base case: split at 0, left is empty
    assert condition[..0] == [];
    assert condition[0..] == condition;
  } else if i == |condition| {
    // Base case: split at end, right is empty
    assert condition[|condition|..] == [];
  } else {
    // Recursive case: process first element and use induction
    var head := condition[0];
    var tail := condition[1..];
    if head {
      CountTrueLemma(tail, i-1);
      assert CountTrue(condition) == 1 + CountTrue(tail);
      assert CountTrue(condition[..i]) == 1 + CountTrue(tail[..i-1]);
      assert CountTrue(condition[i..]) == CountTrue(tail[i-1..]);
    } else {
      CountTrueLemma(tail, i-1);
      assert CountTrue(condition) == CountTrue(tail);
      assert CountTrue(condition[..i]) == CountTrue(tail[..i-1]);
      assert CountTrue(condition[i..]) == CountTrue(tail[i-1..]);
    }
  }
}

/* helper modified by LLM (iteration 5): Fixed GetIthTruePositionLemma with complete inductive proof */
lemma GetIthTruePositionLemma(condition: seq<bool>, i: nat)
  requires i < CountTrue(condition)
  ensures 0 <= GetIthTruePosition(condition, i) < |condition|
  ensures condition[GetIthTruePosition(condition, i)]
  ensures forall j :: 0 <= j < GetIthTruePosition(condition, i) ==> !condition[j]
  decreases |condition|
{
  if |condition| == 0 {
    // Contradiction since i < CountTrue([]) = 0
  } else if condition[0] {
    if i == 0 {
      // Base case: position 0 is the first true
      assert GetIthTruePosition(condition, i) == 0;
    } else {
      // Recursive case for tail with i-1
      GetIthTruePositionLemma(condition[1..], i-1);
      assert GetIthTruePosition(condition, i) == 1 + GetIthTruePosition(condition[1..], i-1);
    }
  } else {
    // Skip false element, i remains the same
    GetIthTruePositionLemma(condition[1..], i);
    assert GetIthTruePosition(condition, i) == 1 + GetIthTruePosition(condition[1..], i);
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
/* code modified by LLM (iteration 5): Fixed implementation with proper loop invariants and lemma applications */
{
  result := [];
  var index := 0;
  var count := 0;
  
  while index < |arr|
    invariant index <= |arr|
    invariant count == CountTrue(condition[..index])
    invariant |result| == count
    invariant forall k :: 0 <= k < count ==>
      result[k] == arr[GetIthTruePosition(condition[..index], k)]
    invariant forall pos :: 0 <= pos < index && condition[pos] ==>
      exists k :: 0 <= k < count && result[k] == arr[pos]
  {
    CountTrueLemma(condition[..index+1], index);
    if condition[index] {
      result := result + [arr[index]];
      count := count + 1;
      GetIthTruePositionLemma(condition[..index+1], count-1);
    }
    index := index + 1;
  }
  
  // Final verification
  assert index == |arr|;
  assert condition[..index] == condition;
  GetIthTruePositionLemma(condition, count-1);
}
// </vc-code>
