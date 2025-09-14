// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function times3(x: int): int { x * 3 }

lemma Times3Divides(x: int) ensures times3(x)/3 == x && times3(x)/3 * 3 == times3(x) { }
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result / 3 == x
    ensures result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  result := times3(x);
}
// </vc-code>
