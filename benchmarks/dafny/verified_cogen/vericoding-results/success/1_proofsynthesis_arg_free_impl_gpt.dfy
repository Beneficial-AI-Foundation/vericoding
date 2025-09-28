// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsOdd(n: int) { n % 2 != 0 }
lemma OddOfOne() ensures IsOdd(1) { }
// </vc-helpers>

// <vc-spec>
method ChooseOdd()
// </vc-spec>
// <vc-code>
{
  var odd := 1;
  assert IsOdd(odd);
}
// </vc-code>
