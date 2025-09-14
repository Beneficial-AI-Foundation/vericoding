// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ChooseOdd(v: array<int>) returns (odd_index: int)
    requires exists q :: 0 <= q < v.Length && v[q] % 2 == 1
    ensures 0 <= odd_index < v.Length
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): added loop invariant to ensure all elements before i are even and unreachable assert at end for verification */
var i := 0;
while i < v.Length
  invariant 0 <= i <= v.Length
  invariant forall k :: 0 <= k < i ==> v[k] % 2 != 1
{
  if v[i] % 2 == 1 {
    odd_index := i;
    return;
  }
  i := i + 1;
}
assert false;
}
// </vc-code>
