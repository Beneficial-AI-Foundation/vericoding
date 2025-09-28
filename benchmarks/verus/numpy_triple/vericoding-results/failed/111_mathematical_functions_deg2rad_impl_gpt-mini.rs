// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): tightened numeric bounds to account for floor division rounding */
fn rad_fits(d: i8)
    ensures
        -128 <= d as int * 314 / 18000,
        d as int * 314 / 18000 <= 127,
{
    proof {
        let di = d as int;
        // d as int is between -128 and 127
        assert(-128 <= di && di <= 127);
        // multiply preserves ordering with positive constant
        assert(di * 314 <= 127 * 314);
        assert(di * 314 >= -128 * 314);
        // division by positive 18000 preserves ordering (monotonicity)
        assert((di * 314) / 18000 <= (127 * 314) / 18000);
        assert((di * 314) / 18000 >= (-128 * 314) / 18000);
        // numeric bounds for the extreme products (accounting for floor division)
        assert((127 * 314) / 18000 <= 2);
        assert((-128 * 314) / 18000 >= -3);
        // combine to get usable bounds for the ratio
        assert(-3 <= (di * 314) / 18000);
        assert((di * 314) / 18000 <= 2);
        // these imply the value fits in i8
        assert(-128 <= (di * 314) / 18000);
        assert((di * 314) / 18000 <= 127);
    }
}

// </vc-helpers>

// <vc-spec>
fn deg2rad(degrees: Vec<i8>) -> (radians: Vec<i8>)
    ensures 
        radians.len() == degrees.len(),
        forall|i: int| 0 <= i < degrees.len() ==> #[trigger] radians@[i] as int == degrees@[i] as int * 314 / 18000
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement loop without assumes and prove invariant using fix j in proof */
    let mut res: Vec<i8> = Vec::new();
    let mut idx: usize = 0;
    while idx < degrees.len()
        invariant
            0 <= idx as int,
            idx as int <= degrees.len() as int,
            res.len() as int == idx as int,
            forall|j: int| 0 <= j < idx as int ==> res@[j] as int == degrees@[j] as int * 314 / 18000,
        decreases degrees.len() as int - idx as int
    {
        let old: usize = idx;
        let oldi: int = old as int;
        let v: int = degrees[old] as int * 314 / 18000;
        rad_fits(degrees[old]);
        res.push(v as i8);
        idx = idx + 1;
        assert(forall|j: int| 0 <= j < idx as int ==> res@[j] as int == degrees@[j] as int * 314 / 18000) by {
            fix j;
            if 0 <= j && j < idx as int {
                if j < oldi {
                    assert(res@[j] as int == degrees@[j] as int * 314 / 18000);
                } else {
                    assert(j == oldi);
                    assert(res@[j] as int == v);
                    assert(v == degrees@[j] as int * 314 / 18000);
                }
            } else {
                assert((0 <= j && j < idx as int) ==> res@[j] as int == degrees@[j] as int * 314 / 18000);
            }
        }
    }
    res
}

// </vc-code>


}
fn main() {}