// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool {
    k > 0 && a.len() == k && (forall|i: int| 0 <= i < k ==> #[trigger] a[i] > 0) && n >= 0
}

spec fn hamsters_transported(n: int, capacity: int) -> int {
    if capacity > 0 {
        capacity * (n / capacity)
    } else {
        0
    }
}

spec fn optimal_solution(n: int, a: Seq<int>, box_type: int, num_boxes: int) -> bool {
    valid_input(n, a.len() as int, a) &&
    1 <= box_type <= a.len() &&
    num_boxes == n / a[box_type - 1] &&
    forall|i: int| 0 <= i < a.len() ==> #[trigger] hamsters_transported(n, a[box_type - 1]) >= #[trigger] hamsters_transported(n, a[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [no changes, just fixing compilation in main code] */
use vstd::arithmetic::div_mod::*;

proof fn lemma_num_boxes_bounds(n: i8, a: &Vec<i8>)
    requires
        n as int >= 0,
        a@.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> (a@[i] as int) > 0,
    ensures
        forall|i: int| 0 <= i < a@.len() ==> 
            0 <= (n as int) / (a@[i] as int) <= 127,
{
    let n_int = n as int;
    let spec_a = a@;
    assert forall|i: int| 0 <= i < spec_a.len() implies 
        0 <= n_int / (spec_a[i] as int) <= 127
    by {
        let capacity = spec_a[i] as int;
        assert(capacity > 0);
        assert(n_int >= 0);

        lemma_div_is_nonnegative(n_int, capacity);

        assert(n_int <= 127); // n is i8
        lemma_div_is_le(n_int, capacity);
        assert(n_int / capacity <= n_int);

        assert(n_int / capacity <= 127);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(n as int, k as int, a@.map(|i, x: i8| x as int))
    ensures ({
        let (box_type, num_boxes) = result;
        1 <= box_type <= k &&
        num_boxes >= 0 &&
        optimal_solution(n as int, a@.map(|i, x: i8| x as int), box_type as int, num_boxes as int)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [fixed compilation error by changing `ghost let` to `let ghost`] */
    let ghost spec_a = a@.map(|_idx, x: i8| x as int);
    let ghost n_int = n as int;

    // From requires: k > 0, so a is not empty.
    let mut best_box_type: i8 = 1;

    let ghost mut max_transported = hamsters_transported(n_int, spec_a[0]);

    let mut i: i8 = 1;
    while i < k
        invariant
            1 <= i <= k,
            1 <= best_box_type <= i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] max_transported >= hamsters_transported(n_int, spec_a[j]),
            max_transported == hamsters_transported(n_int, spec_a[(best_box_type - 1) as int]),
        decreases k - i
    {
        let mut update = false;
        proof {
            let current_capacity = spec_a[i as int];
            let current_transported = hamsters_transported(n_int, current_capacity);
            if current_transported > max_transported {
                update = true;
            }
        }

        if update {
            best_box_type = i + 1;
            proof {
                let current_capacity = spec_a[i as int];
                max_transported = hamsters_transported(n_int, current_capacity);
            }
        }
        i = i + 1;
    }

    let num_boxes = n / a[(best_box_type - 1) as usize];
    
    proof {
        let k_int = k as int;
        lemma_num_boxes_bounds(n, &a);
        let final_best_box_type_int = best_box_type as int;
        let final_num_boxes_int = num_boxes as int;
        let final_best_idx = final_best_box_type_int - 1;

        assert(1 <= final_best_box_type_int <= k_int);
        assert(final_num_boxes_int == n_int / spec_a[final_best_idx]);
        assert(0 <= final_num_boxes_int <= 127);
    
        assert forall|j: int| 0 <= j < k_int implies
            hamsters_transported(n_int, spec_a[final_best_idx]) >= hamsters_transported(n_int, spec_a[j])
        by {
            assert(i == k);
            assert(forall|l: int| 0 <= l < k as int ==> max_transported >= hamsters_transported(n_int, spec_a[l]));
            assert(max_transported == hamsters_transported(n_int, spec_a[final_best_idx]));
        }
        assert(optimal_solution(n_int, spec_a, final_best_box_type_int, final_num_boxes_int));
    }
    
    (best_box_type, num_boxes)
}
// </vc-code>


}

fn main() {}