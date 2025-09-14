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
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant exists q :: i <= q < v.Length && v[q] % 2 == 1
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
