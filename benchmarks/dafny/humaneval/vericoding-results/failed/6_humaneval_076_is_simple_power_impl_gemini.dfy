// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Added assert to PowerDivisibility to prevent timeout and kept PowerDivision] */
lemma PowerDivisibility(x: nat, k: nat)
    requires x > 1
    requires k > 0
    ensures power(x, k) % x == 0
{
    // This equality is true by the definition of power, since k > 0.
    // Making it explicit helps the verifier connect the definition to the % operator.
    assert power(x, k) == x * power(x, k - 1);
}

lemma PowerDivision(x: nat, y1: nat, y2: nat)
    requires x > 0
    requires y1 <= y2
    ensures power(x, y2) == power(x, y1) * power(x, y2 - y1)
    decreases y2 - y1
{
    if y1 < y2 {
       PowerDivision(x, y1, y2 - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [No logical change; convinced errors were due to helper timeout.] */
    if n <= 0 {
        ans := false;
    } else if x == 1 {
        ans := (n == 1);
    } else { // x > 1 and n > 0
        var rem := n as nat;
        var exp: nat := 0;
        while rem > 1 && rem % x == 0
            invariant rem > 0
            invariant n as nat == rem * power(x, exp)
            decreases rem
        {
            rem := rem / x;
            exp := exp + 1;
        }
        ans := (rem == 1);
    }
}
// </vc-code>
