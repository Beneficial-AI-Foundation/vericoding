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
    false
}

#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    // post-conditions-start
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
    // post-conditions-end
{
    let mut c = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
            forall|p: int, q: int| 0 <= p < q < c.len() ==> c[p] != c[q],
    {
        let elem = a[i];
        if !in_array_exec(b, elem) && !in_array_exec(&c, elem) {
            c.push(elem);
        }
    }
    
    c
}

fn main() {}
}