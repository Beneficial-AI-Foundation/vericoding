// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause for array access */
predicate HasOddFrom(a: array<int>, i: int) reads a { 0 <= i <= a.Length && exists k :: i <= k < a.Length && a[k] % 2 == 1 }
// </vc-helpers>

// <vc-spec>
method ChooseOdd(v: array<int>) returns (odd_index: int)
    requires exists q :: 0 <= q < v.Length && v[q] % 2 == 1
    ensures 0 <= odd_index < v.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate to find an odd element using HasOddFrom predicate */
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant HasOddFrom(v, i)
    decreases v.Length - i
  {
    if v[i] % 2 == 1 {
      odd_index := i;
      return;
    }
    var k :| i <= k < v.Length && v[k] % 2 == 1;
    assert k >= i + 1;
    i := i + 1;
  }
  var k2 :| 0 <= k2 < v.Length && v[k2] % 2 == 1;
  odd_index := k2;
}
// </vc-code>
