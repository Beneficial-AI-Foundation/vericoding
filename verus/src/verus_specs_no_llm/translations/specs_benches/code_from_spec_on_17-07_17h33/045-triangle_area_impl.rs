use vstd::prelude::*;

verus! {

//IMPL triangle_area
fn triangle_area(a: u64, h: u64) -> (area: u64)
    /* code modified by LLM (iteration 1): Moved requires and ensures clauses to correct position after function signature */
    requires
        a > 0 &&
        h > 0 &&
        a * h / 2 <= u64::MAX,
    ensures
        area == a * h / 2,
{
    /* code modified by LLM (iteration 1): Implemented correct function body to return triangle area calculation */
    a * h / 2
}

}
fn main() {}