use vstd::prelude::*;

verus! {

spec fn exp(x: int, e: int) -> int
    recommends e >= 0
{
    if e == 0 { 1 } else { x * exp(x, e - 1) }
}

proof fn exp3_Lemma(n: int)
    requires n >= 1
    ensures (exp(3, n) - 1) % 2 == 0
{
}

proof fn mult8_Lemma(n: int)
    requires n >= 1
    ensures (exp(3, 2 * n) - 1) % 8 == 0
{
    if n == 1 {
    } else {
        assert((exp(3, 2 * n) - 1) % 8 == (exp(3, 2 * (n - 1)) * 8 + exp(3, 2 * (n - 1)) - 1) % 8);
        mult8_Lemma(n - 1);
        assert((exp(3, 2 * (n - 1)) * 8 + exp(3, 2 * (n - 1)) - 1) % 8 == 0);
    }
}

}