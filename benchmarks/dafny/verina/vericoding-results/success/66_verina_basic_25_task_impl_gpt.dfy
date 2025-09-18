// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumUpToClosed(n: int): int { if n <= 0 then 0 else n * (n + 1) / 2 }
predicate IsValidN(n: int) { n < 100000 }
// </vc-helpers>

// <vc-spec>
method SumAndAverage(n: int) returns (result: (int, real))
    requires n < 100000  // reasonable bound to prevent overflow
    ensures
        n == 0 ==> result.0 == 0
    ensures
        n > 0 ==> result.0 == (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
  if n <= 0 {
    result := (0, 0.0);
  } else {
    var sum: int := n * (n + 1) / 2;
    var avg: real := (sum as real) / (n as real);
    result := (sum, avg);
  }
}
// </vc-code>
