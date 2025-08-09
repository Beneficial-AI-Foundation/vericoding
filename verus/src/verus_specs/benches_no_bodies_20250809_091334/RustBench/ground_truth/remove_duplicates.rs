use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
    
fn in_array_exec(a: &Vec<i32>, x: i32) -> (result: bool) 
    ensures 
        result == in_array(a@, x),
{
    return false;  // TODO: Remove this line and implement the function body
}

#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() >= 1,
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {}
}