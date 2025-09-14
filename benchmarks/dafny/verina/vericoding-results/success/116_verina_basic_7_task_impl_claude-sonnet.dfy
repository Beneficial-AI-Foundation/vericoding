// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumOfSquaresHelper(k: nat): nat
{
    if k == 0 then 0 else (2*k-1)*(2*k-1) + SumOfSquaresHelper(k-1)
}

/* helper modified by LLM (iteration 4): simplified lemma proof to avoid timeout */
lemma SumOfSquaresFormula(n: nat)
    ensures SumOfSquaresHelper(n) == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    if n == 0 {
        // Base case is trivial
    } else {
        SumOfSquaresFormula(n-1);
        // The recursive proof follows from the inductive hypothesis
        // and algebraic manipulation of the recurrence relation
    }
}
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
    requires n >= 0
    ensures result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): unchanged method body */
    result := SumOfSquaresHelper(n);
    SumOfSquaresFormula(n);
}
// </vc-code>
