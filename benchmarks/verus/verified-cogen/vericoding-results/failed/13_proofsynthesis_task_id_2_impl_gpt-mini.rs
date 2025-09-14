// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): sequence contains predicate using index existential */
spec fn seq_contains(s: Seq<i32>, x: i32) -> bool { exists|i: int| 0 <= i < s.len() && s[i] == x }
// </vc-helpers>

// <vc-spec>
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate without using Vec::contains by manual search */
    let mut res: Vec<i32> = Vec::new();
    for v_ref in list1.iter() {
        let v: i32 = *v_ref;
        let mut found_in_list2: bool = false;
        for w_ref in list2.iter() {
            if *w_ref == v {
                found_in_list2 = true;
            }
        }
        if found_in_list2 {
            let mut found_in_res: bool = false;
            for r_ref in res.iter() {
                if *r_ref == v {
                    found_in_res = true;
                }
            }
            if !found_in_res {
                res.push(v);
            }
        }
    }
    res
}
// </vc-code>

}
fn main() {}