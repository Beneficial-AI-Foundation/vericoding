// <vc-preamble>

function abs(x: int): nat
{
    if x >= 0 then x else -x
}

predicate divides(d: int, n: int)
{
    if d == 0 then n == 0 else n % d == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected an error with an if statement always executing without a return in a lemma (Dafny considers it a parse error). */
lemma EuclidAlgorithm(a: nat, b: nat) returns (g: nat)
    requires a >= 0 && b >= 0
    ensures g > 0 <==> a != 0 || b != 0
    ensures g == 0 <==> a == 0 && b == 0
    ensures divides(g, a) && divides(g, b)
    ensures forall d: int :: d > 0 && divides(d, a) && divides(d, b) ==> d <= g
    decreases a, b
{
    if b == 0 {
        return a;
    } else {
        return EuclidAlgorithm(b, a % b);
    }
}
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (result: nat)
    ensures result > 0 <==> (a != 0 || b != 0)
    ensures result == 0 <==> (a == 0 && b == 0)
    ensures divides(result, a) && divides(result, b)
    ensures forall d: int :: d > 0 && divides(d, a) && divides(d, b) ==> d <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed for the code block. */
{
    var abs_a := abs(a);
    var abs_b := abs(b);

    result := EuclidAlgorithm(abs_a, abs_b);
}
// </vc-code>
