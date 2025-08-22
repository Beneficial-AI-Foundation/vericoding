use vstd::prelude::*;
fn main() {}
verus!{
//IMPL havoc_inline_post
pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
    requires 
        forall |k:int| 0 <= k < old(v).len() ==> old(v)[k] > 0,
        a > 0,
        b == false,
{  
    // Function body can be empty since no postconditions need to be satisfied
}
}