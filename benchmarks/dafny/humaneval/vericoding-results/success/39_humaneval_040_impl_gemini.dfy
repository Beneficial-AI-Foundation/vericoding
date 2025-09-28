// <vc-preamble>

predicate HasTripleSumToZero(l: seq<int>)
{
    exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasTripleSumToZero(l)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): [Refactored to an early-return structure and added assertions] */
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall i_inv, j_inv, k_inv :: 0 <= i_inv < i && i_inv < j_inv < k_inv < |l| ==> l[i_inv] + l[j_inv] + l[k_inv] != 0
  {
    var j := i + 1;
    while j < |l|
      invariant i < j <= |l|
      invariant forall j_inv, k_inv :: i < j_inv < j && j_inv < k_inv < |l| ==> l[i] + l[j_inv] + l[k_inv] != 0
    {
      var k := j + 1;
      while k < |l|
        invariant j < k <= |l|
        invariant forall k_inv :: j < k_inv < k ==> l[i] + l[j] + l[k_inv] != 0
      {
        if l[i] + l[j] + l[k] == 0 {
          assert HasTripleSumToZero(l);
          return true;
        }
        k := k + 1;
      }
      assert forall k_inv :: j < k_inv < |l| ==> l[i] + l[j] + l[k_inv] != 0;
      j := j + 1;
    }
    assert forall j_inv, k_inv :: i < j_inv < |l| && j_inv < k_inv < |l| ==> l[i] + l[j_inv] + l[k_inv] != 0;
    i := i + 1;
  }
  assert forall i_inv, j_inv, k_inv :: 0 <= i_inv < j_inv < k_inv < |l| ==> l[i_inv] + l[j_inv] + l[k_inv] != 0;
  return false;
}
// </vc-code>
