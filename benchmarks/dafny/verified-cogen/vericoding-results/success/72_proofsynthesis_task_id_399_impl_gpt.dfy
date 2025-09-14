// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): xor helper and its definitional lemma to aid quantifier discharge */
function xor32(a: bv32, b: bv32): bv32 { a ^ b }
lemma Xor32Def(a: bv32, b: bv32)
  ensures xor32(a, b) == a ^ b
{ }
// </vc-helpers>

// <vc-spec>
method BitWiseXor(arr1: array<bv32>, arr2: array<bv32>) returns (result: array<bv32>)
    requires arr1.Length == arr2.Length
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] ^ arr2[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): loop computes xor using helper and a quantified invariant; explicit forall after the loop discharges postcondition */
  var n := arr1.Length;
  result := new bv32[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant arr1.Length == n && arr2.Length == n
    invariant forall j :: 0 <= j && j < i ==> result[j] == xor32(arr1[j], arr2[j])
    decreases n - i
  {
    result[i] := xor32(arr1[i], arr2[i]);
    i := i + 1;
  }
  assert i == n;
  forall k | 0 <= k && k < result.Length
    ensures result[k] == arr1[k] ^ arr2[k]
  {
    assert 0 <= k && k < i;
    assert result[k] == xor32(arr1[k], arr2[k]);
    Xor32Def(arr1[k], arr2[k]);
  }
}
// </vc-code>
