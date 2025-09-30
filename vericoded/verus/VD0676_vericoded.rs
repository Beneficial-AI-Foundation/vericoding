// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: &[i32], x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a@.index(i) == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Simplified loop invariant for better proof clarity. */
fn is_in_array(a: &[i32], x: i32) -> (result: bool)
    ensures
        result == in_array(a, x),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            in_array(a, x) <==> (exists|k: int| (i as int) <= k < (a.len() as int) && a@.index(k) == x),
        decreases a.len() - i
    {
        if a[i] == x {
            return true;
        }
        i = i + 1;
    }
    return false;
}

/* helper modified by LLM (iteration 3): Simplified loop invariant for better proof clarity. */
fn contains(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures
        result == v@.contains(x),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            v@.contains(x) <==> (exists|k: int| (i as int) <= k < (v.len() as int) && v@.index(k) == x),
        decreases v.len() - i
    {
        if v[i] == x {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn remove_elements(a: &[i32], b: &[i32]) -> (result: Vec<i32>)

    ensures 
        forall|x: i32| result@.contains(x) ==> in_array(a, x) && !in_array(b, x),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@.index(i) != result@.index(j)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Replaced the overly complex and incorrect loop invariant with a simpler one that matches the postcondition. */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: i32| result@.contains(x) ==> in_array(a, x) && !in_array(b, x),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> result@.index(k) != result@.index(j),
        decreases a.len() - i
    {
        let x = a[i];
        let in_b = is_in_array(b, x);
        let in_result = contains(&result, x);
        if !in_b && !in_result {
            result.push(x);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}