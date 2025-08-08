use vstd::prelude::*;

verus! {

// SPEC  
#[verifier::external_body]
fn diagonal(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<i32>)
    requires 
        arr.len() > 0,
        arr.len() == arr@[0].len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr@[i].len() == arr.len(),
        -arr.len() < k < arr.len(),
    ensures 
        if k > 0 { ret.len() == arr.len() - k } else { ret.len() == arr.len() + k },
        forall|i: int| 0 <= i < ret.len() ==> 
            if k >= 0 { 
                ret@[i] == arr@[i]@[i + k]
            } else { 
                ret@[i] == arr@[i - k]@[i]
            }
{
    unimplemented!()
}

fn main() {}

}