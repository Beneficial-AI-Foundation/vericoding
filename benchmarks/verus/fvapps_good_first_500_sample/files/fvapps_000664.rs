// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn return_number(n: i32) -> (result: i32)
    ensures result == n
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


/* Apps difficulty: interview
   Assurance level: guarded_and_plausible */

}

fn main() {
    // println!("{}", return_number(123));
    // println!("{}", return_number(0)); 
    // println!("{}", return_number(99999));
}