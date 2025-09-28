// <vc-preamble>
// Axiomatic definition of bitwise OR operation on integers
function {:axiom} {:extern} BitwiseOr(x: int, y: int): int

// Axiomatic properties of bitwise OR operation
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): slice length lemma */
lemma SliceLength(arr: array<int>, n: int)
  requires 0 <= n <= arr.Length
  ensures |arr[..n]| == n
{
  assert |arr[..n]| == n;
}

/* helper modified by LLM (iteration 5): slice elements correspond to array elements */
lemma SliceElems(arr: array<int>, n: int)
  requires 0 <= n <= arr.Length
  ensures forall k :: 0 <= k < n ==> arr[..n][k] == arr[k]
{
  assert forall k :: 0 <= k < n ==> arr[..n][k] == arr[k];
}

/* helper modified by LLM (iteration 5): full slice length lemma */
lemma SliceFullLength(arr: array<int>)
  ensures |arr[..]| == arr.Length
{
  assert |arr[..]| == arr.Length;
}

// </vc-helpers>

// <vc-spec>
lemma {:axiom} BitwiseOrZeroRight(x: int)
  ensures BitwiseOr(x, 0) == x

lemma {:axiom} BitwiseOrZeroLeft(x: int)
  ensures BitwiseOr(0, x) == x

lemma {:axiom} BitwiseOrNegOneRight(x: int)
  ensures BitwiseOr(x, -1) == -1

lemma {:axiom} BitwiseOrNegOneLeft(x: int)
  ensures BitwiseOr(-1, x) == -1

lemma {:axiom} BitwiseOrCommutative(x: int, y: int)
  ensures BitwiseOr(x, y) == BitwiseOr(y, x)

lemma {:axiom} BitwiseOrAssociative(x: int, y: int, z: int)
  ensures BitwiseOr(BitwiseOr(x, y), z) == BitwiseOr(x, BitwiseOr(y, z))

lemma {:axiom} BitwiseOrIdempotent(x: int)
  ensures BitwiseOr(x, x) == x

/**
 * Compute the bit-wise OR of two integer vectors element-wise.
 * Takes two sequences of integers of equal length and returns a sequence where each element
 * is the bitwise OR of the corresponding elements from the input sequences.
 */
method BitwiseOrVector(x1: seq<int>, x2: seq<int>) returns (result: seq<int>)
  requires |x1| == |x2|
  ensures |result| == |x1|
  // Basic element-wise operation property
  ensures forall i :: 0 <= i < |result| ==> result[i] == BitwiseOr(x1[i], x2[i])
  // Identity with zero vector (right): if x2[i] == 0, then result[i] == x1[i]
  ensures forall i :: 0 <= i < |result| && x2[i] == 0 ==> result[i] == x1[i]
  // Identity with zero vector (left): if x1[i] == 0, then result[i] == x2[i]
  ensures forall i :: 0 <= i < |result| && x1[i] == 0 ==> result[i] == x2[i]
  // Saturation with -1 (all bits set): if either input is -1, result is -1
  ensures forall i :: 0 <= i < |result| && (x1[i] == -1 || x2[i] == -1) ==> result[i] == -1
  // Commutativity: BitwiseOrVector(x1, x2) produces same result as BitwiseOrVector(x2, x1)
  ensures forall i :: 0 <= i < |result| ==> result[i] == BitwiseOr(x2[i], x1[i])
  // Idempotency: if vectors are equal, result equals the input
  ensures (forall i :: 0 <= i < |x1| ==> x1[i] == x2[i]) ==> 
          (forall i :: 0 <= i < |result| ==> result[i] == x1[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute element-wise BitwiseOr and prove all ensures using lemmas */
{
  var n := |x1|;
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> arr[j] == BitwiseOr(x1[j], x2[j])
  {
    arr[i] := BitwiseOr(x1[i], x2[i]);
    i := i + 1;
  }
  assert i == n;
  assert forall j :: 0 <= j < n ==> arr[j] == BitwiseOr(x1[j], x2[j]);
  result := arr[..n];
  SliceLength(arr, n);
  SliceElems(arr, n);
  assert |result| == n;
  assert forall k :: 0 <= k < |result| ==> result[k] == BitwiseOr(x1[k], x2[k]);

  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall t :: 0 <= t < k ==> ( (x2[t] == 0 ==> result[t] == x1[t])
                                          && (x1[t] == 0 ==> result[t] == x2[t])
                                          && ((x1[t] == -1 || x2[t] == -1) ==> result[t] == -1)
                                          && (result[t] == BitwiseOr(x2[t], x1[t])) )
  {
    if x2[k] == 0 {
      assert result[k] == BitwiseOr(x1[k], x2[k]);
      assert BitwiseOr(x1[k], x2[k]) == BitwiseOr(x1[k], 0);
      BitwiseOrZeroRight(x1[k]);
      assert BitwiseOr(x1[k], 0) == x1[k];
      assert result[k] == x1[k];
    }
    if x1[k] == 0 {
      assert result[k] == BitwiseOr(x1[k], x2[k]);
      assert BitwiseOr(x1[k], x2[k]) == BitwiseOr(0, x2[k]);
      BitwiseOrZeroLeft(x2[k]);
      assert BitwiseOr(0, x2[k]) == x2[k];
      assert result[k] == x2[k];
    }
    if x1[k] == -1 || x2[k] == -1 {
      assert result[k] == BitwiseOr(x1[k], x2[k]);
      if x1[k] == -1 {
        BitwiseOrNegOneLeft(x2[k]);
        assert BitwiseOr(-1, x2[k]) == -1;
        assert BitwiseOr(x1[k], x2[k]) == -1;
      } else {
        BitwiseOrNegOneRight(x1[k]);
        assert BitwiseOr(x1[k], -1) == -1;
        assert BitwiseOr(x1[k], x2[k]) == -1;
      }
      assert result[k] == -1;
    }
    BitwiseOrCommutative(x1[k], x2[k]);
    assert BitwiseOr(x1[k], x2[k]) == BitwiseOr(x2[k], x1[k]);
    assert result[k] == BitwiseOr(x2[k], x1[k]);
    k := k + 1;
  }

  assert forall i :: 0 <= i < |result| && x2[i] == 0 ==> result[i] == x1[i];
  assert forall i :: 0 <= i < |result| && x1[i] == 0 ==> result[i] == x2[i];
  assert forall i :: 0 <= i < |result| && (x1[i] == -1 || x2[i] == -1) ==> result[i] == -1;
  assert forall i :: 0 <= i < |result| ==> result[i] == BitwiseOr(x2[i], x1[i]);

  if forall i :: 0 <= i < |x1| ==> x1[i] == x2[i] {
    var m := 0;
    while m < n
      invariant 0 <= m <= n
      invariant forall t :: 0 <= t < m ==> result[t] == x1[t]
    {
      assert result[m] == BitwiseOr(x1[m], x2[m]);
      assert x1[m] == x2[m];
      BitwiseOrIdempotent(x1[m]);
      assert BitwiseOr(x1[m], x1[m]) == x1[m];
      assert BitwiseOr(x1[m], x2[m]) == x1[m];
      assert result[m] == x1[m];
      m := m + 1;
    }
    assert forall i :: 0 <= i < |result| ==> result[i] == x1[i];
  }
}

// </vc-code>
