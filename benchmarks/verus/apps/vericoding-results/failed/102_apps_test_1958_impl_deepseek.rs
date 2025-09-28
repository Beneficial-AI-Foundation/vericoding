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
/* helper modified by LLM (iteration 5): Fixed string comparison syntax with string literal format */
proof fn lemma_compute_total_payment_backward_base(buyers: Seq<&str>, p: int, current_apples: int)
    requires p >= 0, p % 2 == 0,
              forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus",
              current_apples >= 0
    ensures compute_payment_backward(buyers, p, -1, current_apples) == 0
{
}

proof fn lemma_compute_payment_backward_recursive(buyers: Seq<&str>, p: int, idx: int, current_apples: int)
    requires p >= 0, p % 2 == 0,
              0 <= idx < buyers.len(),
              current_apples >= 0,
              forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures compute_payment_backward(buyers, p, idx, current_apples) == {
        let new_apples = if buyers[idx] == "halfplus" { current_apples * 2 + 1 } else { current_apples * 2 };
        let payment = if buyers[idx] == "halfplus" { (new_apples / 2) * p } else { current_apples * p };
        payment + compute_payment_backward(buyers, p, idx - 1, new_apples)
    }
{
}

proof fn lemma_payment_nonnegative(buyers: Seq<&str>, p: int, idx: int, current_apples: int)
    requires p >= 0, p % 2 == 0,
              -1 <= idx < buyers.len(),
              current_apples >= 0,
              forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures compute_payment_backward(buyers, p, idx, current_apples) >= 0
    decreases idx + 1
{
    if idx >= 0 {
        lemma_payment_nonnegative(buyers, p, idx - 1, if buyers[idx] == "halfplus" { current_apples * 2 + 1 } else { current_apples * 2 });
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
    /* code modified by LLM (iteration 5): Fixed string comparison with enum-like approach */
    let mut current_apples: i32 = 0;
    let mut total_payment: i32 = 0;
    let mut i: usize = buyers.len();
    
    proof {
        lemma_compute_total_payment_backward_base(buyers@, p as int, 0);
        lemma_payment_nonnegative(buyers@, p as int, buyers.len() as int - 1, 0);
    }
    
    while i > 0
        invariant
            i <= buyers.len(),
            total_payment as int + compute_payment_backward(buyers@, p as int, i as int - 1, current_apples as int) == 
                compute_payment_backward(buyers@, p as int, buyers.len() as int - 1, 0),
            current_apples >= 0
        decreases i
    {
        i -= 1;
        
        proof {
            lemma_compute_payment_backward_recursive(buyers@, p as int, i as int, current_apples as int);
        }
        
        let buyer = buyers[i];
        let halfplus_str: &str = "halfplus";
        let new_apples = if *buyer == *halfplus_str {
            current_apples * 2 + 1
        } else {
            current_apples * 2
        };
        
        let p_i32 = p as i32;
        let payment = if *buyer == *halfplus_str {
            (new_apples / 2) * p_i32
        } else {
            current_apples * p_i32
        };
        
        total_payment += payment;
        current_apples = new_apples;
    }
    
    (total_payment as i8)
}
// </vc-code>


}

fn main() {}