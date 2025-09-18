// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn area_sum_spec(y: Seq<i32>, dx: i32, k: nat) -> int
    requires
        y.len() > 0,
        dx > 0,
        k <= y.len() - 1,
    decreases k
{
    if k == 0 {
        0
    } else {
        let i = (k-1) as int;
        area_sum_spec(y, dx, (k-1) as nat) + (dx as int * (y[i] + y[i+1])) / 2
    }
}

proof fn lemma_constant_y(y: Seq<i32>, dx: i32, k: nat)
    requires
        y.len() > 0,
        dx > 0,
        k <= y.len() - 1,
        forall|i: int| 0 <= i < y.len() ==> #[trigger] y[i] == y[0],
    ensures
        area_sum_spec(y, dx, k) == dx as int * k as int * y[0],
    decreases k
{
    if k > 0 {
        lemma_constant_y(y, dx, (k-1) as nat);
        vstd::arithmetic::power_of_2::lemma_mul_div_two(dx as int * y[0] as int);
    }
}

proof fn lemma_non_negative_y(y: Seq<i32>, dx: i32, k: nat)
    requires
        y.len() > 0,
        dx > 0,
        k <= y.len() - 1,
        forall|i: int| 0 <= i < y.len() ==> #[trigger] y[i] >= 0,
    ensures
        area_sum_spec(y, dx, k) >= 0,
    decreases k
{
    if k > 0 {
        lemma_non_negative_y(y, dx, (k-1) as nat);
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
    if y.len() < 2 {
        return 0;
    }

    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < y.len() - 1
        invariant
            dx > 0,
            y.len() > 1,
            0 <= i <= y.len() - 1,
            sum as int == area_sum_spec(y.view(), dx, i as nat),
    {
        let term = (dx * (y[i] + y[i+1])) / 2;
        sum = sum + term;
        i = i + 1;
    }

    proof {
        let k = (y.len() - 1) as nat;
        if forall|j: int| 0 <= j < y.len() ==> #[trigger] y[j] == y[0] {
            lemma_constant_y(y.view(), dx, k);
        }
        if forall|j: int| 0 <= j < y.len() ==> #[trigger] y[j] >= 0 {
            lemma_non_negative_y(y.view(), dx, k);
        }
    }

    sum
}
// </vc-code>

}
fn main() {}