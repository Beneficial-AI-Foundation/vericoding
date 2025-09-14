// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause to fix termination error */
#[verifier::loop_isolation(false)]
fn does_contain(v: &Vec<i32>, x: i32) -> (b: bool)
    ensures
        b == in_array(v@, x),
{
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i ==> v[j] != x,
        decreases v.len() - i
    {
        if v[i] == x {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added an explicit trigger to fix the quantifier error */
    let mut c: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c@[k]) && !in_array(b@, c@[k]),
            forall|k: int, l: int| 0 <= k < l < c.len() ==> c@[k] != c@[l],
            forall|k: int| 0 <= k < c.len() ==> (exists|m: int| 0 <= m < i && a@[m] == #[trigger]c@[k]),
        decreases a.len() - i
    {
        let elem = a[i];
        let is_in_b = does_contain(b, elem);
        if !is_in_b {
            let is_in_c = does_contain(&c, elem);
            if !is_in_c {
                c.push(elem);
            }
        }
        i = i + 1;
    }
    c
}
// </vc-code>

}
fn main() {}