// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumUpTo(n: int): int
    ensures n <= 0 ==> SumUpTo(n) == 0
    ensures n > 0 ==> SumUpTo(n) == (n * (n + 1)) / 2
{
    if n > 0 then (n * (n + 1)) / 2 else 0
}
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
  var s: int;
  if n <= 0 {
    s := 0;
    result := (s, 0.0);
  } else {
    s := (n * (n + 1)) / 2;
    var avg: real := (s as real) / (n as real);
    result := (s, avg);
  }
}
// </vc-code>
