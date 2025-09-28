// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(base: int, height: int) -> bool {
    base >= 0 && height >= 0
}

spec fn triangle_area_formula(base: int, height: int) -> int {
    (base * height) / 2
}

spec fn triangle_area(a: int, h: int) -> int {
    (a * h) / 2
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): non-negativity of product/2 */
spec fn prod_div2_nonneg(base: int, height: int) -> bool {
    base >= 0 && height >= 0 ==> (base * height) / 2 >= 0
}

/* helper modified by LLM (iteration 5): area zero when base or height is zero */
spec fn zero_area_lemma(base: int, height: int) -> bool {
    (base == 0 || height == 0) ==> ((base * height) / 2 == 0)
}
// </vc-helpers>

// <vc-spec>
fn calculate_triangle_area(base: u8, height: u8) -> (area: u8)
    requires 
        valid_input(base as int, height as int)
    ensures 
        area as int >= 0,
        area as int == triangle_area_formula(base as int, height as int),
        (base == 0 || height == 0) ==> area == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute area using u16 runtime arithmetic and prove equivalence to spec */
    let prod: u16 = (base as u16) * (height as u16);
    let area_u16: u16 = prod / 2;
    let area: u8 = area_u16 as u8;
    proof {
        let a = base as int;
        let h = height as int;
        assert((prod as int) == a * h);
        assert((area_u16 as int) == (a * h) / 2);
        assert((area as int) == (a * h) / 2);
        assert(prod_div2_nonneg(a, h));
        assert(zero_area_lemma(a, h));
    }
    area
}
// </vc-code>


}

fn main() {}