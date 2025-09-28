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
/* helper modified by LLM (iteration 5): Simplified lemmas and added proper Euclidean algorithm implementation */
lemma EuclideanStep(a: nat, b: nat)
    requires b > 0
    ensures divides(a, b) && divides(a, a % b) <==> divides(a, b) && divides(a, a)
    ensures gcd_euclidean(b, a % b) == gcd_euclidean(a, b)
{
}

function gcd_euclidean(a: nat, b: nat): nat
    requires a > 0 || b > 0
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a
    else if a >= b then gcd_euclidean(a - b, b)
    else gcd_euclidean(a, b - a)
}

lemma GcdProperties(a: nat, b: nat)
    requires a > 0 || b > 0
    ensures var g := gcd_euclidean(a, b); g > 0
    ensures var g := gcd_euclidean(a, b); divides(g, a) && divides(g, b)
    ensures var g := gcd_euclidean(a, b); forall d: int :: d > 0 && divides(d, a) && divides(d, b) ==> d <= g
{
    if a == 0 {
        assert gcd_euclidean(a, b) == b;
    } else if b == 0 {
        assert gcd_euclidean(a, b) == a;
    } else {
        if a >= b {
            GcdProperties(a - b, b);
        } else {
            GcdProperties(a, b - a);
        }
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
{
    /* code modified by LLM (iteration 5): Direct implementation using subtraction-based GCD */
    if a == 0 && b == 0 {
        result := 0;
    } else {
        var x := abs(a);
        var y := abs(b);
        
        result := gcd_euclidean(x, y);
        GcdProperties(x, y);
    }
}
// </vc-code>
