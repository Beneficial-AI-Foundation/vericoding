// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn trapezoid_helper(y: Seq<i8>, dx: i8, area: i8, i: int) -> (result: i8)
    requires
        y.len() > 0,
        dx > 0,
        0 <= i < y.len() as int,
        area >= 0,
    ensures
        result >= 0,
{
    if i == y.len() as int - 1 {
        area
    } else {
        let y_i: i8 = y[i as usize] as i8;
        let y_i1: i8 = y[(i + 1) as usize] as i8;
        let term: i8 = (dx * (y_i + y_i1)) / 2;
        let next_area: i8 = area + term;
        trapezoid_helper(y, dx, next_area, i + 1)
    }
}

/* helper modified by LLM (iteration 5): Fixed type conversion between int and usize */
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
    /* code modified by LLM (iteration 5): Fixed type conversion issues in while loop */
    let mut area: i8 = 0;
    let mut i: usize = 1;
    
    while i < y.len()
        invariant
            1 <= i <= y@.len(),
            area >= 0
        decreases y@.len() - i
    {
        let prev_val: i8 = y[i - 1];
        let curr_val: i8 = y[i];
        let term: i8 = (dx * (prev_val + curr_val)) / 2;
        area = area + term;
        i = i + 1;
    }
    
    area
}
// </vc-code>

}
fn main() {}