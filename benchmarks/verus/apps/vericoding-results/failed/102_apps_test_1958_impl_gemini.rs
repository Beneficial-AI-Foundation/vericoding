// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, p: int, buyers: Seq<&str>) -> bool {
    1 <= n <= 40 &&
    2 <= p <= 1000 &&
    p % 2 == 0 &&
    buyers.len() == n &&
    forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
}

spec fn compute_total_payment(buyers: Seq<&str>, p: int) -> int
    recommends p >= 0,
                p % 2 == 0,
                forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
{
    compute_payment_backward(buyers, p, buyers.len() - 1, 0)
}

spec fn compute_payment_backward(buyers: Seq<&str>, p: int, current_index: int, current_apples: int) -> int
    recommends p >= 0,
                p % 2 == 0,
                -1 <= current_index < buyers.len(),
                current_apples >= 0,
                forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    decreases current_index + 1
{
    if current_index < 0 {
        0
    } else {
        let new_apples = if buyers[current_index] == "halfplus" { 
                            current_apples * 2 + 1
                         } else { 
                            current_apples * 2
                         };
        let payment = if buyers[current_index] == "halfplus" { 
                          (new_apples / 2) * p
                       } else { 
                          current_apples * p
                       };
        payment + compute_payment_backward(buyers, p, current_index - 1, new_apples)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, buyers: Vec<&str>) -> (result: i8)
    requires valid_input(n as int, p as int, buyers@)
    ensures result >= 0,
            result as int == compute_total_payment(buyers@, p as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [Fix compilation error from string comparison] */
    let mut i = (n - 1) as isize;
    let mut ca: i128 = 0;
    let mut total_payment: i128 = 0;
    let p_val = p as i128;

    let ghost n_int = n as int;
    let ghost p_int = p as int;

    while i >= 0
        invariant
            valid_input(n as int, p as int, buyers@),
            -1 <= i < n_int,
            ca >= 0,
            total_payment as int + compute_payment_backward(buyers@, p_int, i as int, ca as int) == compute_total_payment(buyers@, p_int),
        decreases i
    {
        proof {
            let i_int = i as int;
            let ca_int = ca as int;
            if buyers@[i_int] == "halfplus" {
                assert((ca_int * 2 + 1) / 2 == ca_int);
            }
        }

        let i_int = i as int;
        let is_halfplus = spec_to_bool(buyers@[i_int] == "halfplus");

        let payment = if is_halfplus {
            let new_apples = 2 * ca + 1;
            (new_apples / 2) * p_val
        } else {
            ca * p_val
        };
        total_payment = total_payment + payment;

        if is_halfplus {
            ca = 2 * ca + 1;
        } else {
            ca = 2 * ca;
        };
        
        i = i - 1;
    }

    assert(total_payment as int == compute_total_payment(buyers@, p as int));
    
    total_payment as i8
}
// </vc-code>


}

fn main() {}