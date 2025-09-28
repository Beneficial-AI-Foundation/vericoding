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
/* helper modified by LLM (iteration 5): ensures k-th true position lies inside the prefix and that position is true */
lemma GetIthTruePosition_Prefix(condition: seq<bool>, n: nat, k: nat)
    requires n <= |condition|
    requires k < CountTrue(condition[..n])
    ensures GetIthTruePosition(condition[..n], k) < n
    ensures condition[GetIthTruePosition(condition[..n], k)]
    decreases n
{
    if n == 0 {
        // unreachable because k < CountTrue(empty) is false
        return;
    }
    var s := condition[..n];
    if s[0] {
        if k == 0 {
            // by definition of GetIthTruePosition when first is true and i == 0
            assert GetIthTruePosition(s, k) == 0;
            assert 0 < n;
            assert s[0];
            return;
        } else {
            // s[0] is true and k >= 1
            assert CountTrue(s) == 1 + CountTrue(s[1..]);
            assert k < CountTrue(s);
            assert k - 1 < CountTrue(s[1..]);
            // recurse on the tail: condition[1..] has length at least n-1
            GetIthTruePosition_Prefix(condition[1..], n - 1, k - 1);
            assert GetIthTruePosition(s, k) == 1 + GetIthTruePosition(s[1..], k - 1);
            assert GetIthTruePosition(s, k) < n;
            assert s[GetIthTruePosition(s, k)];
            return;
        }
    } else {
        // s[0] is false
        assert CountTrue(s) == CountTrue(s[1..]);
        assert k < CountTrue(s[1..]);
        GetIthTruePosition_Prefix(condition[1..], n - 1, k);
        assert GetIthTruePosition(s, k) == 1 + GetIthTruePosition(s[1..], k);
        assert GetIthTruePosition(s, k) < n;
        assert s[GetIthTruePosition(s, k)];
        return;
    }
}

/* helper modified by LLM (iteration 5): the last true in a prefix is at position n when appended */
lemma GetIthTruePosition_AppendIsLast(condition: seq<bool>, n: nat)
    requires n < |condition|
    requires condition[n]
    ensures GetIthTruePosition(condition[..n+1], CountTrue(condition[..n])) == n
    decreases n
{
    if n == 0 {
        // base case: the first element is true
        assert CountTrue(condition[..0]) == 0;
        assert GetIthTruePosition(condition[..1], 0) == 0;
        return;
    }
    var s := condition[..n+1];
    // Let cprev be the number of trues in the prefix of length n
    var cprev := CountTrue(condition[..n]);
    if s[0] {
        // first of s is true, so the k-th true in s corresponds to 1 + the (k-1)-th true in the tail
        // recursive call on the tail (condition[1..]) with n-1
        GetIthTruePosition_AppendIsLast(condition[1..], n - 1);
        // by definition of GetIthTruePosition when s[0] is true and k = cprev >= 1
        assert cprev >= 1;
        assert GetIthTruePosition(s, cprev) == 1 + GetIthTruePosition(s[1..], cprev - 1);
        // from the recursive call the inner position equals n-1, so overall equals n
        assert 1 + GetIthTruePosition(s[1..], cprev - 1) == n;
        return;
    } else {
        // first of s is false: the k-th true in s corresponds to 1 + the k-th true in the tail
        GetIthTruePosition_AppendIsLast(condition[1..], n - 1);
        assert GetIthTruePosition(s, cprev) == 1 + GetIthTruePosition(s[1..], cprev);
        assert 1 + GetIthTruePosition(s[1..], cprev) == n;
        return;
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
  /* code modified by LLM (iteration 5): build result by iterating over true-count indices using GetIthTruePosition */
  var m := CountTrue(condition);
  var k := 0;
  var res: seq<int> := [];
  while k < m
    invariant 0 <= k <= m
    invariant |res| == k
    invariant forall j :: 0 <= j < k ==> (
      var pos := GetIthTruePosition(condition, j);
      pos < |arr| && condition[pos] && res[j] == arr[pos]
    )
    decreases m - k
  {
    // Ensure the k-th true position is within the full prefix (length |condition|)
    GetIthTruePosition_Prefix(condition, |condition|, k);
    var pos := GetIthTruePosition(condition, k);
    assert pos < |condition|;
    assert condition[pos];
    res := res + [arr[pos]];
    k := k + 1;
  }
  result := res;
}

// </vc-code>
