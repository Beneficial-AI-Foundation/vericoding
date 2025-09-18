// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix nat casting and ensure proper type usage */
spec fn trapezoid_sum(y: Seq<i32>, dx: i32, n: nat) -> (sum: i32)
    requires
        n <= y.len(),
        dx > 0,
    ensures
        sum == dx * (
            if n <= 1 {
                0
            } else {
                (y[0] + y[(n - 1) as int]) / 2 + (if n > 2 { seq_range_sum(y, 1, (n - 1) as int) } else { 0 })
            }
        ),
    decreases n
{
    if n <= 1 {
        0
    } else {
        let prev_sum = trapezoid_sum(y, dx, (n - 1) as nat);
        if n == 1 {
            prev_sum
        } else if n == 2 {
            prev_sum + dx * (y[0] + y[1]) / 2
        } else {
            prev_sum + dx * (y[(n - 2) as int] + y[(n - 1) as int]) / 2
        }
    }
}

spec fn seq_range_sum(y: Seq<i32>, start: int, end: int) -> i32
    requires
        0 <= start <= end <= y.len(),
    decreases (end - start) as nat
{
    if start >= end {
        0
    } else {
        y[start] + seq_range_sum(y, start + 1, end)
    }
}

proof fn constant_sequence_property(y: Seq<i32>, value: i32)
    requires
        forall|i: int| 0 <= i < y.len() ==> y[i] == value,
    ensures
        seq_range_sum(y, 0, y.len() as int) == value * (y.len() as i32),
    decreases y.len() as nat
{
    if y.len() > 0 {
        constant_sequence_property(y.subrange(1, y.len() as int), value);
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
/* code modified by LLM (iteration 5): Remove nat/int casting from executable code, use usize indexing */
{
    let n = y.len();
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            total == dx * (
                if i == 0 {
                    0
                } else {
                    (y[0] + y[i]) / 2 + (if i > 1 { seq_range_sum(y@, 1, i as int) } else { 0 })
                }
            )
    {
        let avg: i32 = (y[i] + y[i + 1]) / 2;
        total = total + dx * avg;
        i = i + 1;
    }
    
    proof {
        if forall|k: int| 0 <= k < y.len() as int ==> y[k] == y[0] {
            constant_sequence_property(y@, y[0]);
        }
    }
    
    total
}
// </vc-code>

}
fn main() {}