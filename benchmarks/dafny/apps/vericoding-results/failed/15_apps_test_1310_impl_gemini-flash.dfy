// <vc-preamble>
predicate ValidInput(arr: seq<bv32>)
{
    |arr| > 0
}

predicate IsMaxXorSubarray(arr: seq<bv32>, result: bv32)
    requires ValidInput(arr)
{
    exists i, j :: 0 <= i <= j < |arr| && result == XorRange(arr, i, j) &&
    forall i1, j1 :: 0 <= i1 <= j1 < |arr| ==> 
        (XorRange(arr, i1, j1) as int) <= (result as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added termination clause for XorRange function. */
function XorRange(arr: seq<bv32>, i: int, j: int): bv32
    requires 0 <= i <= j < |arr|
    decreases j - i
{
    if i == j then arr[i]
    else arr[i] ^ XorRange(arr, i + 1, j)
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by changing `result := 0bv32; return;` to just `result := 0bv32;` as ValidInput already ensures arr is not empty. */
{
  var max_xor: bv32;
  // ValidInput ensures |arr| > 0, so no need to handle `|arr| == 0` explicitly.

  max_xor := arr[0]; 

  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    // Invariant: max_xor holds the maximum xor sum of all subarrays (prefix or complete) examined so far up to index i-1.
    invariant exists k_prev, l_prev :: 0 <= k_prev < |arr| && 0 <= l_prev < |arr| && k_prev <= l_prev && l_prev < i 
                ==> (max_xor as int) >= (XorRange(arr, k_prev, l_prev) as int)
    decreases |arr| - i
  {
    var current_xor: bv32 := 0bv32;
    var j := i;
    while j < |arr|
      invariant i <= j <= |arr|
      // Invariant: current_xor holds the XOR sum of the subarray arr[i..j-1] if j > i, else 0 if j == i
      invariant (j == i ==> current_xor == 0bv32)
      invariant (j > i ==> current_xor == XorRange(arr, i, j-1))
      // Invariant: max_xor is the maximum XOR sum seen so far from arr[k..l] where i <= k <= l < j or k < i.
      invariant forall k_inner, l_inner :: i <= k_inner <= l_inner < j ==> (max_xor as int) >= (XorRange(arr, k_inner, l_inner) as int)
      decreases |arr| - j
    {
      current_xor := current_xor ^ arr[j];
      if (current_xor as int) > (max_xor as int) {
        max_xor := current_xor;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := max_xor;
}
// </vc-code>
