// <vc-preamble>
// Method to raise a Hermite series to a power
// The input coefficients represent a Hermite polynomial series: c[0]*P_0 + c[1]*P_1 + ... + c[n-1]*P_{n-1}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed unresolved identifier 'seq_init' by using the correct Dafny sequence constructor. */
function min(a: nat, b: nat): nat {
    if a < b then a else b
}

function Factorial(k: nat): nat {
    if k == 0 then 1 else k * Factorial(k - 1)
}

function Binomial(n: nat, k: nat): nat 
    requires k <= n
    decreases n
{
    if k == 0 || k == n then 1 
    else Binomial(n-1, k-1) + Binomial(n-1, k)
}

function Exp2(k: nat): real
{
    if k == 0 then 1.0 else 2.0 * Exp2(k-1)
}

method HermeMul(a: seq<real>, b: seq<real>) returns (r: seq<real>)
    requires |a| >= 1 && |b| >= 1
    ensures |r| == |a| + |b| - 1
{
    var result_len := |a| + |b| - 1;
    r := seq<real>(result_len, _ => 0.0);

    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |r| == result_len
    {
        var j := 0;
        while j < |b|
            invariant 0 <= j <= |b|
            invariant |r| == result_len
        {
            if a[i] != 0.0 && b[j] != 0.0 {
                var k := 0;
                while k <= min(i, j)
                    invariant 0 <= k <= min(i, j) + 1
                    invariant |r| == result_len
                    invariant i < |a| && j < |b|
                {
                    var h_index := i + j - 2*k;
                    var term_coeff := Exp2(k) * (Factorial(k) as real) * (Binomial(i,k) as real) * (Binomial(j,k) as real);
                    r := r[h_index := r[h_index] + a[i] * b[j] * term_coeff];
                    k := k + 1;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method HermePow(c: seq<real>, pow: nat, maxpower: nat) returns (result: seq<real>)
    requires pow <= maxpower
    requires maxpower <= 16
    requires |c| >= 1 // Input must be non-empty for meaningful polynomial operations
    ensures |result| == 1 + (|c| - 1) * pow // Unified length formula for all cases
    ensures pow == 0 ==> result[0] == 1.0
    ensures pow == 1 ==> result == c
    ensures pow == 0 ==> forall i :: 1 <= i < |result| ==> result[i] == 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Retaining iterative multiplication logic; primary fix was in helper compilation. */
  if pow == 0 {
    result := [1.0];
  } else if pow == 1 {
    result := c;
  } else {
    var current_coeffs := c;
    var p: nat := 1;
    while p < pow
      invariant 1 <= p <= pow
      invariant |c| >= 1
      invariant |current_coeffs| == 1 + (|c| - 1) * p
      decreases pow - p
    {
        current_coeffs := HermeMul(current_coeffs, c);
        p := p + 1;
    }
    result := current_coeffs;
  }
}
// </vc-code>
