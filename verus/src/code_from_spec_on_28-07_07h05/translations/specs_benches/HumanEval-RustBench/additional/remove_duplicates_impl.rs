use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

fn in_array_exec(a: &Vec<i32>, x: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == in_array(a@, x),
    // post-conditions-end
{
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> a[j] != x,
    {
        if a[i] == x {
            return true;
        }
    }
    return false;
}

#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
{
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
    {
        let mut found = false;
        for j in 0..result.len()
            invariant
                forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]),
                forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
                found == exists|k: int| 0 <= k < j && result[k] == a[i as int],
        {
            if result[j] == a[i] {
                found = true;
                break;
            }
        }
        
        if !found {
            result.push(a[i]);
        }
    }
    
    result
}

fn main() {}
}