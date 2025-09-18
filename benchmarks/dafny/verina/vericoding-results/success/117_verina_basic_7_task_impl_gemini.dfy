// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumFormula(n: nat): int {
    (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
}

lemma SumFormulaInductiveStep(i: nat)
    ensures SumFormula(i) + (2 * i as int + 1) * (2 * i as int + 1) == SumFormula(i + 1)
{}
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
    requires n >= 0
    ensures result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i: nat := 0;
    while i < n
        invariant i <= n
        invariant result as int == SumFormula(i)
    {
        SumFormulaInductiveStep(i);
        result := result + (2 * i + 1) * (2 * i + 1);
        i := i + 1;
    }
}
// </vc-code>
