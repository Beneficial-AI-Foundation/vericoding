use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
    
fn in_array_exec(a: &Vec<i32>, x: i32) -> (result: bool) 
    ensures 
        result == in_array(a@, x),
{
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> a[j] != x,
    {
        if a[i] == x {
            return true;
        }
    }
    false
}

#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() >= 1,
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|k: int| 0 <= k < result.len() ==> in_array(a@, result[k]),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
    {
        if !in_array_exec(&result, a[i]) {
            result.push(a[i]);
        }
    }
    
    result
}

fn main() {}
}