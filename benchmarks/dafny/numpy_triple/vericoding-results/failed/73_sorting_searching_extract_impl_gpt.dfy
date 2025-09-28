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
/* helper modified by LLM (iteration 2): prove CountTrue over snoc via induction with explicit unfolding */
lemma Lemma_CountTrue_SnocElem(s: seq<bool>, b: bool)
  ensures CountTrue(s + [b]) == CountTrue(s) + (if b then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
    // CountTrue([] + [b]) == (if b then 1 else 0) and CountTrue([]) == 0
  } else {
    Lemma_CountTrue_SnocElem(s[1..], b);
    assert CountTrue(s) == (if s[0] then 1 else 0) + CountTrue(s[1..]);
    assert CountTrue(s + [b]) == (if s[0] then 1 else 0) + CountTrue((s + [b])[1..]);
    assert (s + [b])[1..] == s[1..] + [b];
    assert CountTrue(s + [b]) == (if s[0] then 1 else 0) + (CountTrue(s[1..]) + (if b then 1 else 0));
    assert CountTrue(s + [b]) == ((if s[0] then 1 else 0) + CountTrue(s[1..])) + (if b then 1 else 0);
    assert CountTrue(s + [b]) == CountTrue(s) + (if b then 1 else 0);
  }
}

/* helper modified by LLM (iteration 2): preserve ith-true position when appending at end */
lemma Lemma_GetIth_Snoc_Preserve(s: seq<bool>, b: bool, k: nat)
  requires k < CountTrue(s)
  ensures GetIthTruePosition(s + [b], k) == GetIthTruePosition(s, k)
  decreases |s|
{
  if |s| == 0 {
  } else if s[0] {
    if k == 0 {
      assert GetIthTruePosition(s, 0) == 0;
      assert GetIthTruePosition(s + [b], 0) == 0;
    } else {
      assert CountTrue(s) == 1 + CountTrue(s[1..]);
      assert k - 1 < CountTrue(s[1..]);
      Lemma_GetIth_Snoc_Preserve(s[1..], b, k - 1);
      assert GetIthTruePosition(s, k) == 1 + GetIthTruePosition(s[1..], k - 1);
      assert (s + [b])[1..] == s[1..] + [b];
      assert GetIthTruePosition(s + [b], k) == 1 + GetIthTruePosition(s[1..] + [b], k - 1);
    }
  } else {
    assert CountTrue(s) == CountTrue(s[1..]);
    assert k < CountTrue(s[1..]);
    Lemma_GetIth_Snoc_Preserve(s[1..], b, k);
    assert GetIthTruePosition(s, k) == 1 + GetIthTruePosition(s[1..], k);
    assert (s + [b])[1..] == s[1..] + [b];
    assert GetIthTruePosition(s + [b], k) == 1 + GetIthTruePosition(s[1..] + [b], k);
  }
}

/* helper modified by LLM (iteration 2): show last appended true becomes the next ith-true position */
lemma Lemma_GetIth_SnocLast(s: seq<bool>)
  ensures CountTrue(s) < CountTrue(s + [true])
  ensures GetIthTruePosition(s + [true], CountTrue(s)) == |s|
  decreases |s|
{
  Lemma_CountTrue_SnocElem(s, true);
  if |s| == 0 {
    // CountTrue([]) == 0, GetIthTruePosition([true], 0) == 0 == |[]|
  } else if s[0] {
    Lemma_GetIth_SnocLast(s[1..]);
    assert CountTrue(s) == 1 + CountTrue(s[1..]);
    assert (s + [true])[1..] == s[1..] + [true];
    assert GetIthTruePosition(s + [true], CountTrue(s))
           == 1 + GetIthTruePosition(s[1..] + [true], CountTrue(s[1..]));
    assert |s| == 1 + |s[1..]|;
  } else {
    Lemma_GetIth_SnocLast(s[1..]);
    assert CountTrue(s) == CountTrue(s[1..]);
    assert (s + [true])[1..] == s[1..] + [true];
    assert GetIthTruePosition(s + [true], CountTrue(s))
           == 1 + GetIthTruePosition(s[1..] + [true], CountTrue(s[1..]));
    assert |s| == 1 + |s[1..]|;
  }
}

/* helper modified by LLM (iteration 2): bound of ith-true is within sequence length */
lemma Lemma_GetIth_Bounds(s: seq<bool>, k: nat)
  requires k < CountTrue(s)
  ensures GetIthTruePosition(s, k) < |s|
  decreases |s|
{
  if |s| == 0 {
  } else if s[0] {
    if k == 0 {
      assert GetIthTruePosition(s, 0) == 0;
      assert 0 < |s|;
    } else {
      assert CountTrue(s) == 1 + CountTrue(s[1..]);
      assert k - 1 < CountTrue(s[1..]);
      Lemma_GetIth_Bounds(s[1..], k - 1);
      assert GetIthTruePosition(s, k) == 1 + GetIthTruePosition(s[1..], k - 1);
      assert GetIthTruePosition(s[1..], k - 1) < |s[1..]|;
      assert 1 + GetIthTruePosition(s[1..], k - 1) < 1 + |s[1..]|;
      assert |s| == 1 + |s[1..]|;
    }
  } else {
    assert CountTrue(s) == CountTrue(s[1..]);
    assert k < CountTrue(s[1..]);
    Lemma_GetIth_Bounds(s[1..], k);
    assert GetIthTruePosition(s, k) == 1 + GetIthTruePosition(s[1..], k);
    assert GetIthTruePosition(s[1..], k) < |s[1..]|;
    assert 1 + GetIthTruePosition(s[1..], k) < 1 + |s[1..]|;
    assert |s| == 1 + |s[1..]|;
  }
}

/* helper modified by LLM (iteration 2): the ith-true position indeed indexes a true element */
lemma Lemma_GetIth_IsTrue(s: seq<bool>, k: nat)
  requires k < CountTrue(s)
  ensures s[GetIthTruePosition(s, k)]
  decreases |s|
{
  Lemma_GetIth_Bounds(s, k);
  if |s| == 0 {
  } else if s[0] {
    if k == 0 {
      // s[0] is true
    } else {
      assert CountTrue(s) == 1 + CountTrue(s[1..]);
      assert k - 1 < CountTrue(s[1..]);
      Lemma_GetIth_IsTrue(s[1..], k - 1);
      Lemma_GetIth_Bounds(s[1..], k - 1);
      assert GetIthTruePosition(s, k) == 1 + GetIthTruePosition(s[1..], k - 1);
      assert s[1..][GetIthTruePosition(s[1..], k - 1)];
      assert s[1 + GetIthTruePosition(s[1..], k - 1)] == s[1..][GetIthTruePosition(s[1..], k - 1)];
      assert s[GetIthTruePosition(s, k)];
    }
  } else {
    assert CountTrue(s) == CountTrue(s[1..]);
    assert k < CountTrue(s[1..]);
    Lemma_GetIth_IsTrue(s[1..], k);
    Lemma_GetIth_Bounds(s[1..], k);
    assert GetIthTruePosition(s, k) == 1 + GetIthTruePosition(s[1..], k);
    assert s[1..][GetIthTruePosition(s[1..], k)];
    assert s[1 + GetIthTruePosition(s[1..], k)] == s[1..][GetIthTruePosition(s[1..], k)];
    assert s[GetIthTruePosition(s, k)];
  }
}

/* helper modified by LLM (iteration 2): ith-true positions are strictly increasing in k */
lemma Lemma_IthPositionsStrictlyIncreasing(s: seq<bool>, k1: nat, k2: nat)
  requires k1 < k2 < CountTrue(s)
  ensures GetIthTruePosition(s, k1) < GetIthTruePosition(s, k2)
  decreases |s|
{
  if |s| == 0 {
  } else if s[0] {
    if k1 == 0 {
      // GetIthTruePosition(s, 0) == 0
      if k2 == 0 {
        // impossible since k1 < k2
      } else {
        assert GetIthTruePosition(s, 0) == 0;
        assert GetIthTruePosition(s, k2) == 1 + GetIthTruePosition(s[1..], k2 - 1);
        assert 0 < GetIthTruePosition(s, k2);
      }
    } else {
      assert CountTrue(s) == 1 + CountTrue(s[1..]);
      assert k1 - 1 < k2 - 1 < CountTrue(s[1..]);
      Lemma_IthPositionsStrictlyIncreasing(s[1..], k1 - 1, k2 - 1);
      assert GetIthTruePosition(s, k1) == 1 + GetIthTruePosition(s[1..], k1 - 1);
      assert GetIthTruePosition(s, k2) == 1 + GetIthTruePosition(s[1..], k2 - 1);
    }
  } else {
    assert CountTrue(s) == CountTrue(s[1..]);
    assert k1 < k2 < CountTrue(s[1..]);
    Lemma_IthPositionsStrictlyIncreasing(s[1..], k1, k2);
    assert GetIthTruePosition(s, k1) == 1 + GetIthTruePosition(s[1..], k1);
    assert GetIthTruePosition(s, k2) == 1 + GetIthTruePosition(s[1..], k2);
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
  /* code modified by LLM (iteration 2): loop builds result while preserving mapping to ith-true positions; added asserts to discharge lemma preconditions and postconditions */
  var i: nat := 0;
  result := [];
  while i < |arr|
    invariant i <= |arr|
    invariant |result| == CountTrue(condition[..i])
    invariant forall k: nat :: k < |result| ==> GetIthTruePosition(condition[..i], k) < i
    invariant forall k: nat :: k < |result| ==> result[k] == arr[GetIthTruePosition(condition[..i], k)]
    invariant forall j: nat :: j < i && condition[j] ==> exists k: nat :: k < |result| && result[k] == arr[j]
    decreases |arr| - i
  {
    if condition[i] {
      var oldLen := |result|;
      assert oldLen == CountTrue(condition[..i]);
      forall k: nat | k < oldLen {
        Lemma_GetIth_Snoc_Preserve(condition[..i], true, k);
      }
      result := result + [arr[i]];
      assert |result| == oldLen + 1;
      Lemma_CountTrue_SnocElem(condition[..i], true);
      Lemma_GetIth_SnocLast(condition[..i]);
      // New element corresponds to position i
      assert GetIthTruePosition(condition[..(i + 1)], oldLen) == i;
      assert result[oldLen] == arr[i];
      // Extend coverage invariant for j == i
      assert exists k: nat :: k < |result| && result[k] == arr[i];
      i := i + 1;
    } else {
      assert |result| == CountTrue(condition[..i]);
      forall k: nat | k < |result| {
        Lemma_GetIth_Snoc_Preserve(condition[..i], false, k);
      }
      Lemma_CountTrue_SnocElem(condition[..i], false);
      i := i + 1;
    }
  }
  // Establish global properties using lemmas on full condition
  assert i == |arr|;
  assert |arr| == |condition|;
  assert |result| == CountTrue(condition);
  forall k: nat | k < |result| {
    Lemma_GetIth_Bounds(condition, k);
    Lemma_GetIth_IsTrue(condition, k);
  }
  forall k1: nat, k2: nat | k1 < k2 && k2 < |result| {
    Lemma_IthPositionsStrictlyIncreasing(condition, k1, k2);
  }
}
// </vc-code>
