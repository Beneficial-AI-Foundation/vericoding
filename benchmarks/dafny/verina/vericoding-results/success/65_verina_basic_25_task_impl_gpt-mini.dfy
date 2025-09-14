// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): closed-form sum helper */
function SumClosed(n: int): int { if n <= 0 then 0 else n * (n + 1) / 2 }

/* helper modified by LLM (iteration 3): average as real, handles n<=0 */
function Average(sum: int, n: int): real { if n <= 0 then 0.0 else sum as real / n as real }
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
  /* code modified by LLM (iteration 3): compute sum via SumClosed and average via Average */
  var s := SumClosed(n);
  var avg := Average(s, n);
  result := (s, avg);
}

// </vc-code>
