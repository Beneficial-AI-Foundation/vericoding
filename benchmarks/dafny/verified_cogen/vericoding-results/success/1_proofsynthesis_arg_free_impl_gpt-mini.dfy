// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsOdd(n: int): bool { n % 2 != 0 }

function One(): int { 1 }

lemma OneIsOdd() ensures IsOdd(One()) { }
// </vc-helpers>

// <vc-spec>
method ChooseOdd()
// </vc-spec>
// <vc-code>
{
  var n := One();
  assert IsOdd(n);
}
// </vc-code>
