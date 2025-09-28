// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn sum_range(y: &Seq<i8>, start: int, end: int) -> int
    requires
        0 <= start <= end,
        end <= y.len(),
    ensures
        start == end ==> sum_range(y, start, end) == 0,
    decreases end - start
{
    if start >= end {
        0int
    } else {
        let val: int = (*y)[end - 1] as int;
        let rec: int = sum_range(y, start, end - 1);
        val + rec
    }
}
// </vc-helpers>

// <vc-spec>
fn trapezoid(y: Vec<i8>, dx: i8) -> (result: i8)
    requires 
        y.len() > 0,
        dx > 0,
    ensures
        (forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] == y@[0]) ==> 
            result as int == dx as int * (y.len() - 1) as int * y@[0],
        (forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] >= 0) ==> result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixes trapezoid calculation without helper */
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    
    while i < y.len() - 1
        invariant
            0 <= i <= y.len() - 1,
            sum >= 0,
    {
        sum = sum + dx * y[i];
        i = i + 1;
    }
    
    sum
}
// </vc-code>

}
fn main() {}