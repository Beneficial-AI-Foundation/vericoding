use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

fn in_array_exec(a: &Vec<i32>, x: i32) -> (result: bool)
    ensures
        result == in_array(a@, x),
{
    for i in 0..a.len()
        invariant
            /* code modified by LLM (iteration 1): fixed invariant to correctly track searched elements */
            forall|k: int| 0 <= k < i ==> a[k] != x,
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
            forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        let mut found = false;
        for j in 0..result.len()
            invariant
                forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]),
                forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
                /* code modified by LLM (iteration 1): fixed invariants to properly track search progress */
                found ==> exists|k: int| 0 <= k < j && result[k] == a[i as int],
                !found ==> forall|k: int| 0 <= k < j ==> result[k] != a[i as int],
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

/* code modified by LLM (iteration 1): Fixed compilation errors by:
*/