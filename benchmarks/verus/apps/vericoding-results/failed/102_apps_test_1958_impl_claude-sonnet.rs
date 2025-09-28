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
/* helper modified by LLM (iteration 5): using proper string comparison with equal function */
fn str_equal(s1: &str, s2: &str) -> (result: bool)
    ensures result == (s1 == s2)
{
    vstd::string::str_slice_eq(s1, s2)
}

fn compute_payment_backward_exec(buyers: &Vec<&str>, p: i32, current_index: i32, current_apples: i32) -> (payment: i32)
    requires
        p >= 0,
        p % 2 == 0,
        -1 <= current_index < buyers.len(),
        current_apples >= 0,
        forall|i: int| 0 <= i < buyers@.len() ==> buyers@[i] == "half" || buyers@[i] == "halfplus"
    ensures
        payment == compute_payment_backward(buyers@, p as int, current_index as int, current_apples as int)
    decreases current_index + 1
{
    if current_index < 0 {
        0
    } else {
        let buyer = buyers[current_index as usize];
        let new_apples = if str_equal(buyer, "halfplus") {
            current_apples * 2 + 1
        } else {
            current_apples * 2
        };
        let payment = if str_equal(buyer, "halfplus") {
            (new_apples / 2) * p
        } else {
            current_apples * p
        };
        payment + compute_payment_backward_exec(buyers, p, current_index - 1, new_apples)
    }
}

/* helper modified by LLM (iteration 5): fixed lemma keyword usage */
fn total_payment_equiv(buyers: Seq<&str>, p: int)
    requires
        p >= 0,
        p % 2 == 0,
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures
        compute_total_payment(buyers, p) == compute_payment_backward(buyers, p, buyers.len() - 1, 0)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, buyers: Vec<&str>) -> (result: i8)
    requires valid_input(n as int, p as int, buyers@)
    ensures result >= 0,
            result as int == compute_total_payment(buyers@, p as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type compatibility for p parameter */
    let total = compute_payment_backward_exec(&buyers, p as i32, (n - 1) as i32, 0);
    
    proof {
        total_payment_equiv(buyers@, p as int);
    }
    
    total as i8
}
// </vc-code>


}

fn main() {}