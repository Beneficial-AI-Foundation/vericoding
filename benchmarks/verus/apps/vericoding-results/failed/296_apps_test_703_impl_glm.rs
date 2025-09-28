// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn valid_input(k: int, a: int, b: int, v: int) -> bool {
    2 <= k <= 1000 && 1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= v <= 1000
}

spec fn box_capacity(num_boxes: int, k: int, b: int, v: int) -> int
    recommends num_boxes >= 0
{
    v * (num_boxes + min(b, (k - 1) * num_boxes))
}

spec fn can_store_nuts(num_boxes: int, k: int, a: int, b: int, v: int) -> bool
    recommends num_boxes >= 0
{
    a <= box_capacity(num_boxes, k, b, v)
}

spec fn is_minimal_solution(result: int, k: int, a: int, b: int, v: int) -> bool
    recommends result >= 1
{
    can_store_nuts(result, k, a, b, v) &&
    (result == 1 || !can_store_nuts(result - 1, k, a, b, v))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added exec min function for i32 */
fn exec_min(x: i32, y: i32) -> i32 {
    if x < y { x } else { y }
}
// </vc-helpers>

// <vc-spec>
fn solve(k: i8, a: i8, b: i8, v: i8) -> (result: i8)
    requires
        valid_input(k as int, a as int, b as int, v as int)
    ensures
        result >= 1,
        result <= 127,
        is_minimal_solution(result as int, k as int, a as int, b as int, v as int),
        exists|i: int| 1 <= i <= 127 && can_store_nuts(i, k as int, a as int, b as int, v as int) && result as int == i && 
            (forall|j: int| 1 <= j < i ==> !can_store_nuts(j, k as int, a as int, b as int, v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by avoiding problematic cast expressions in proof blocks */
    let mut i: i8 = 1;
    while i <= 127
        invariant
            1 <= i <= 128,
            forall|j: int| 1 <= j < i ==> !can_store_nuts(j, k as int, a as int, b as int, v as int)
        decreases 128 - (i as int)
    {
        let k_int = k as i32;
        let a_int = a as i32;
        let b_int = b as i32;
        let v_int = v as i32;
        let i_int = i as i32;

        let term1 = (k_int - 1) * i_int;
        let term2 = exec_min(b_int, term1);
        let capacity_exec = v_int * (i_int + term2);
        
        if a_int <= capacity_exec {
            proof {
                reveal(box_capacity);
                let term1_spec = (k as int - 1) * (i as int);
                let term2_spec = min(b as int, term1_spec);
                let capacity_spec = (v as int) * ( (i as int) + term2_spec );

                assert(term1 as int == term1_spec);

                if b_int < term1 {
                    assert(term2 == b_int);
                    assert(term2 as int == b as int);
                    assert(b as int < term1_spec);
                    assert(term2_spec == b as int);
                    assert(term2 as int == term2_spec);
                } else {
                    assert(term2 == term1);
                    assert(term2 as int == term1_spec);
                    assert(term2_spec == term1 as int);
                    assert(term2 as int == term2_spec);
                }

                assert((i_int + term2) as int == (i as int) + (term2 as int));
                assert((v_int * (i_int + term2)) as int == (v as int) * ( (i as int) + (term2 as int) ));
                assert(capacity_exec as int == capacity_spec);
                assert(capacity_spec == box_capacity(i as int, k as int, b as int, v as int));

                assert(a as int <= capacity_exec as int);
                assert(a as int <= box_capacity(i as int, k as int, b as int, v as int));
            }
            return i;
        } else {
            proof {
                reveal(box_capacity);
                let term1_spec = (k as int - 1) * (i as int);
                let term2_spec = min(b as int, term1_spec);
                let capacity_spec = (v as int) * ( (i as int) + term2_spec );

                assert(term1 as int == term1_spec);

                if b_int < term1 {
                    assert(term2 == b_int);
                    assert(term2 as int == b as int);
                    assert(b as int < term1_spec);
                    assert(term2_spec == b as int);
                    assert(term2 as int == term2_spec);
                } else {
                    assert(term2 == term1);
                    assert(term2 as int == term1_spec);
                    assert(term2_spec == term1 as int);
                    assert(term2 as int == term2_spec);
                }

                assert((i_int + term2) as int == (i as int) + (term2 as int));
                assert((v_int * (i_int + term2)) as int == (v as int) * ( (i as int) + (term2 as int) ));
                assert(capacity_exec as int == capacity_spec);
                assert(capacity_spec == box_capacity(i as int, k as int, b as int, v as int));

                assert(a as int > capacity_exec as int);
                assert(a as int > box_capacity(i as int, k as int, b as int, v as int));
            }
        }
        i += 1;
    }
    proof {
        assert(false);
    }
    return 127;
}
// </vc-code>


}

fn main() {}