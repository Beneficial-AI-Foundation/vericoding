use vstd::prelude::*;

verus! {

fn less(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires 
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res@[i] == (a@[i] < b@[i]),
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}

fn main() {}