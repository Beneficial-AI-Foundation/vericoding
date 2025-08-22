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
            forall|j: int| 0 <= j < i ==> a@[j] != x,
    {
        if a[i] == x {
            return true;
        }
    }
    false
}

#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
{
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]) && !in_array(b@, result[k]),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] != result[q],
    {
        let element = a[i];
        
        if !in_array_exec(b, element) && !in_array_exec(&result, element) {
            result.push(element);
        }
    }
    
    result
}

fn main() {}
}