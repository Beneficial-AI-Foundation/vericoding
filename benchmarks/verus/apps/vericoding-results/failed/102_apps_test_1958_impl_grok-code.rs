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
pub spec fn valid_input(n: int, p: int, buyers: Seq<&str>) -> bool {
    1 <= n <= 40 &&
    2 <= p <= 1000 &&
    p % 2 == 0 &&
    buyers.len() == n &&
    forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
}

/* helper modified by LLM (iteration 5): added pub spec fn for compute_total_payment */
pub spec fn compute_total_payment(buyers: Seq<&str>, p: int) -> int
    recommends
        p >= 0,
        p % 2 == 0,
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
{
    compute_payment_backward(buyers, p, buyers.len() - 1, 0)
}

/* helper modified by LLM (iteration 5): added pub spec fn for compute_payment_backward */
pub spec fn compute_payment_backward(buyers: Seq<&str>, p: int, current_index: int, current_apples: int) -> int
    recommends
        p >= 0,
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

/* helper modified by LLM (iteration 5): recursive exec helper with spec ensures */
pub fn compute_total_payment_exec(buyers: &Vec<&str>, p: i64) -> (result: i64)
    requires
        p >= 0,
        p % 2 == 0,
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures
        (result as int) == compute_total_payment(buyers@, p as int),
        result >= 0
{
    if buyers.len() == 0 {
        0
    } else {
        compute_payment_backward_exec(buyers, p, buyers.len() as isize - 1, 0)
    }
}

/* helper modified by LLM (iteration 5): recursive exec helper with spec ensures */
pub fn compute_payment_backward_exec(buyers: &Vec<&str>, p: i64, current_index: isize, current_apples: i64) -> (result: i64)
    requires
        p >= 0,
        p % 2 == 0,
        -1 <= current_index && current_index < buyers.len() as isize,
        current_apples >= 0,
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures
        (result as int) == compute_payment_backward(buyers@, p as int, current_index as int, current_apples as int),
        result >= 0
    decreases current_index + 1
{
    if current_index < 0 {
        0
    } else {
        let i = current_index as usize;
        let new_apples = if buyers[i] == "halfplus" { current_apples * 2 + 1 } else { current_apples * 2 };
        let payment = if buyers[i] == "halfplus" { (new_apples / 2) * p } else { current_apples * p };
        payment + compute_payment_backward_exec(buyers, p, current_index - 1, new_apples)
    }
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
    /* code modified by LLM (iteration 5): implemented solve by calling exec helper and casting */
    let result = compute_total_payment_exec(&buyers, p as i64) as i8;
    result
}
// </vc-code>


}

fn main() {}