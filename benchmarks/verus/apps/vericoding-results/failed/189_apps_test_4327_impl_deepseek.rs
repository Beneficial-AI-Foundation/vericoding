// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, p: int) -> bool {
    0 <= a <= 100 && 0 <= p <= 100
}

spec fn total_pieces(a: int, p: int) -> int
    recommends valid_input(a, p)
{
    a * 3 + p
}

spec fn max_pies(a: int, p: int) -> int
    recommends valid_input(a, p)
{
    total_pieces(a, p) / 2
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_div_mod(x: int, d: int)
    requires
        d > 0,
    ensures
        x == d * (x / d) + (x % d),
        x % d >= 0,
        x % d < d
{
    /* helper modified by LLM (iteration 5): Fixed division lemma implementation */
    assert(x == d * (x / d) + (x % d));
    assert(x % d >= 0);
    assert(x % d < d);
}

proof fn lemma_total_pieces_nonnegative(a: int, p: int)
    requires
        valid_input(a, p),
    ensures
        total_pieces(a, p) >= 0
{
    /* helper modified by LLM (iteration 5): Actual proof */
    assert(0 <= a <= 100 && 0 <= p <= 100);
    assert(total_pieces(a, p) == a * 3 + p);
    assert(a * 3 >= 0);
    assert(a * 3 + p >= 0);
}

proof fn lemma_max_pies_nonnegative(a: int, p: int)
    requires
        valid_input(a, p),
    ensures
        max_pies(a, p) >= 0
{
    /* helper modified by LLM (iteration 5): Actual proof */
    lemma_total_pieces_nonnegative(a, p);
    assert(total_pieces(a, p) >= 0);
    assert(max_pies(a, p) >= 0);
}

proof fn lemma_div_inequality(a: int, p: int)
    requires
        valid_input(a, p),
    ensures
        (a * 3 + p) / 2 == max_pies(a, p)
{
    /* helper modified by LLM (iteration 5): Actual proof */
    assert(max_pies(a, p) == total_pieces(a, p) / 2);
    assert(total_pieces(a, p) == a * 3 + p);
}
// </vc-helpers>

// <vc-spec>
fn calculate_max_pies(a: i8, p: i8) -> (pies: i8)
    requires 
        valid_input(a as int, p as int)
    ensures 
        pies as int == max_pies(a as int, p as int) &&
        pies >= 0 &&
        pies as int == (a as int * 3 + p as int) / 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed assertion and return value */
    proof {
        let total_int = (a as int) * 3 + (p as int);
        let pies_int = total_int / 2;
        lemma_max_pies_nonnegative(a as int, p as int);
        lemma_div_inequality(a as int, p as int);
        assert(pies_int >= 0);
        assert(pies_int == max_pies(a as int, p as int));
        assert(total_int >= 0 && total_int <= 400);
        assert(pies_int <= 200);
        assert(pies_int <= 0x7F);
        assert(pies_int as i8 >= 0);
    }
    let total: i32 = (a as i32) * 3 + (p as i32);
    (total / 2) as i8
}
// </vc-code>


}

fn main() {}