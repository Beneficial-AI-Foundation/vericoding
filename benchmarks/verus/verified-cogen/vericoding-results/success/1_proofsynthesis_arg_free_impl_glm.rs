// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): changed return type from int to i32 to fix ghost type error */
fn get_odd() -> i32 { 1 }
// </vc-helpers>

// <vc-spec>
fn choose_odd()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): calling helper with correct type */
    let _x = get_odd();
}
// </vc-code>

}
fn main() {}