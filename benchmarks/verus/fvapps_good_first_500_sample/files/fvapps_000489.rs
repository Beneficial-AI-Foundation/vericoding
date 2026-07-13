// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calculate(s: String) -> (result: Option<i32>)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    None
    // impl-end
}
// </vc-code>


}

fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible
    
    // println!("{:?}", calculate("3+2*2".to_string()));  // Should output: Some(7)
    // println!("{:?}", calculate(" 3/2 ".to_string()));  // Should output: Some(1) 
    // println!("{:?}", calculate(" 3+5 / 2 ".to_string()));  // Should output: Some(5)
}