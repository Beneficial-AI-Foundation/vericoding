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
/* helper modified by LLM (iteration 5): [removed unused helper] */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, buyers: Vec<&str>) -> (result: i8)
    requires valid_input(n as int, p as int, buyers@)
    ensures result >= 0,
            result as int == compute_total_payment(buyers@, p as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [fixed `int` and `nat` type errors by removing unnecessary casting, using `as int` only when passing arguments to ghost functions] */
    let mut total_payment: int = 0;
    let mut current_apples: int = 0;

    let mut i: int = (n as int) - 1;
    while i >= 0
        invariant
            0 <= i + 1 <= n as int,
            (p as int) % 2 == 0,
            current_apples >= 0,
            total_payment == compute_total_payment(buyers@, p as int) - compute_payment_backward(buyers@, p as int, i, current_apples),
            forall|j: int| 0 <= j < n as int ==> (buyers@[j] == "half" || buyers@[j] == "halfplus"),
        decreases i
    {
        let buyer_type = buyers.get(i);

        let new_apples = if buyer_type == Some("halfplus") {
            current_apples * 2 + 1
        } else {
            current_apples * 2
        };

        let payment = if buyer_type == Some("halfplus") {
            (new_apples / 2) * (p as int)
        } else {
            current_apples * (p as int)
        };

        total_payment = total_payment + payment;
        current_apples = new_apples;
        i = i - 1;
    }

    total_payment as i8
}
// </vc-code>


}

fn main() {}