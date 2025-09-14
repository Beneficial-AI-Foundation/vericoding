// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsOdd(n: int) {
  n % 2 != 0
}
// </vc-helpers>

// <vc-spec>
method ChooseOdd()
// </vc-spec>
// <vc-code>
{
  var x := 3;
  assert IsOdd(x);
}
// </vc-code>
