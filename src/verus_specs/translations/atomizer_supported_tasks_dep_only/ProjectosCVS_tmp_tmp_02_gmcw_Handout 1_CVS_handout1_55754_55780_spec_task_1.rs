use vstd::prelude::*;

verus! {

proof fn peasant_mult_lemma(a: int, b: int)
    requires b >= 0
    ensures b % 2 == 0 ==> (a * b == 2 * a * b / 2)
    ensures b % 2 == 1 ==> (a * b == a + 2 * a * (b - 1) / 2)
{
}

pub fn peasant_mult(a: int, b: int) -> (r: int)
    requires(b > 0)
    ensures(r == a * b)
{
}

}