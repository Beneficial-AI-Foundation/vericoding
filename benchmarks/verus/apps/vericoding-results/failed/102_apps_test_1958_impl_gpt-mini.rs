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
/* helper modified by LLM (iteration 4): placeholder no-op helper */
spec fn _llm_helper_noop() {
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
    /* code modified by LLM (iteration 4): fixed tracked variable declarations and loop invariants, added proof of correctness */
    let mut i: usize = buyers.len();
    let tracked mut acc: int = 0;
    let mut acc_rt: i64 = 0;
    let tracked mut current_index: int = (buyers@).len() as int - 1;
    let tracked mut current_apples: int = 0;
    let mut current_apples_rt: i64 = 0;
    while i > 0
        invariant
            0 <= acc,
            current_apples >= 0,
            acc + compute_payment_backward(buyers@, p as int, current_index, current_apples) == compute_total_payment(buyers@, p as int),
            current_index + 1 == i as int,
            acc == acc_rt as int,
            current_apples == current_apples_rt as int,
        decreases i
    {
        i = i - 1;
        let buyer = buyers[i];
        if buyer == "halfplus" {
            let new_apples_tracked: int = current_apples * 2 + 1;
            let new_apples_rt: i64 = current_apples_rt * 2 + 1;
            let payment_tracked: int = (new_apples_tracked / 2) * (p as int);
            let payment_rt: i64 = (new_apples_rt / 2) * (p as i64);
            acc = acc + payment_tracked;
            acc_rt = acc_rt + payment_rt;
            current_apples = new_apples_tracked;
            current_apples_rt = new_apples_rt;
        } else {
            let new_apples_tracked: int = current_apples * 2;
            let new_apples_rt: i64 = current_apples_rt * 2;
            let payment_tracked: int = current_apples * (p as int);
            let payment_rt: i64 = current_apples_rt * (p as i64);
            acc = acc + payment_tracked;
            acc_rt = acc_rt + payment_rt;
            current_apples = new_apples_tracked;
            current_apples_rt = new_apples_rt;
        }
        current_index = current_index - 1;
    }
    proof {
        assert(current_index + 1 == 0 as int);
        assert(current_index == -1);
        assert(compute_payment_backward(buyers@, p as int, current_index, current_apples) == 0);
        assert(acc + 0 == compute_total_payment(buyers@, p as int));
        assert(acc == compute_total_payment(buyers@, p as int));
        assert(acc == acc_rt as int);
    }
    let result_rt: i64 = acc_rt;
    result_rt as i8
}

// </vc-code>


}

fn main() {}