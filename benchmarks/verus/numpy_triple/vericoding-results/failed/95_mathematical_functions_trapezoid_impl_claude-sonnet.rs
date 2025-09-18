// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed requires/ensures from spec function */
spec fn sum_trapezoid_areas(y: Vec<i32>, dx: i32, n: nat) -> int
    decreases n
{
    if n <= 1 {
        0
    } else {
        dx as int * (y[(n-2) as int] + y[(n-1) as int]) / 2 + sum_trapezoid_areas(y, dx, (n-1) as nat)
    }
}

proof fn sum_constant_lemma(y: Vec<i32>, dx: i32, n: nat, val: i32)
    requires 
        n <= y.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] y[i] == val,
        dx > 0
    ensures 
        n > 0 ==> sum_trapezoid_areas(y, dx, n) == dx as int * (n - 1) as int * val as int
    decreases n
{
    if n <= 1 {
    } else {
        sum_constant_lemma(y, dx, (n-1) as nat, val);
    }
}

proof fn sum_nonneg_lemma(y: Vec<i32>, dx: i32, n: nat)
    requires 
        n <= y.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] y[i] >= 0,
        dx > 0
    ensures 
        sum_trapezoid_areas(y, dx, n) >= 0
    decreases n
{
    if n <= 1 {
    } else {
        sum_nonneg_lemma(y, dx, (n-1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn trapezoid(y: Vec<i32>, dx: i32) -> (result: i32)
    requires 
        y.len() > 0,
        dx > 0,
    ensures
        (forall|i: int| 0 <= i < y.len() ==> #[trigger] y[i] == y[0]) ==> 
            result == dx * (y.len() - 1) as i32 * y[0],
        (forall|i: int| 0 <= i < y.len() ==> #[trigger] y[i] >= 0) ==> result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotations to forall quantifiers */
    let mut total: i32 = 0;
    let mut i: usize = 1;
    
    while i < y.len()
        invariant
            1 <= i <= y.len(),
            total == sum_trapezoid_areas(y, dx, i as nat)
        decreases y.len() - i
    {
        total = total + dx * (y[i-1] + y[i]) / 2;
        i = i + 1;
    }
    
    proof {
        if forall|j: int| 0 <= j < y.len() ==> #[trigger] y[j] == y[0] {
            sum_constant_lemma(y, dx, y.len() as nat, y[0]);
        }
        if forall|j: int| 0 <= j < y.len() ==> #[trigger] y[j] >= 0 {
            sum_nonneg_lemma(y, dx, y.len() as nat);
        }
    }
    
    total
}
// </vc-code>

}
fn main() {}