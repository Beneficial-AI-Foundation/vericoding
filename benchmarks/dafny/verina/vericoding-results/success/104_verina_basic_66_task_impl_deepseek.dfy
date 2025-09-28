// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function abs(n: int): int { if n < 0 then -n else n }

function isEvenHelper(n: int): bool 
  requires n >= 0
  decreases n
  { if n == 0 then true else if n == 1 then false else isEvenHelper(n - 2) }

/* helper modified by LLM (iteration 3): Added abs function for proper modular arithmetic handling */
// </vc-helpers>

// <vc-spec>
method ComputeIsEven(x: int) returns (result: bool)
    ensures result == true <==> x % 2 == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Use modulo operation directly for correct even/odd determination */
  result := x % 2 == 0;
}
// </vc-code>
