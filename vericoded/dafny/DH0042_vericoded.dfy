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
  /* code modified by LLM (iteration 2): Fixed loop invariants to properly track checked triples */
  if |l| < 3 {
    return false;
  }
  
  for i := 0 to |l| - 2
    invariant 0 <= i <= |l| - 2
    invariant forall a, b, c :: 0 <= a < b < c < |l| && a < i ==> l[a] + l[b] + l[c] != 0
  {
    for j := i + 1 to |l| - 1
      invariant i + 1 <= j <= |l| - 1
      invariant forall a, b, c :: 0 <= a < b < c < |l| && a < i ==> l[a] + l[b] + l[c] != 0
      invariant forall b, c :: i < b < c < |l| && b < j ==> l[i] + l[b] + l[c] != 0
    {
      for k := j + 1 to |l|
        invariant j + 1 <= k <= |l|
        invariant forall a, b, c :: 0 <= a < b < c < |l| && a < i ==> l[a] + l[b] + l[c] != 0
        invariant forall b, c :: i < b < c < |l| && b < j ==> l[i] + l[b] + l[c] != 0
        invariant forall c :: j < c < |l| && c < k ==> l[i] + l[j] + l[c] != 0
      {
        if l[i] + l[j] + l[k] == 0 {
          return true;
        }
      }
    }
  }
  return false;
}
// </vc-code>
