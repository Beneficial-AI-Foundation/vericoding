// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): count true values in prefix with int indices */
fn prefix_true_count(condition: &Vec<bool>, m: int) -> int
    requires
        0 <= m,
        m <= condition@.len(),
    decreases
        m,
{
    if m == 0 {
        0
    } else {
        let prev = prefix_true_count(condition, m - 1);
        match condition.get((m - 1) as usize) {
            Some(&b) => if b { prev + 1 } else { prev },
            None => prev,
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn extract(condition: &Vec<bool>, arr: &Vec<i8>) -> (result: Vec<i8>)
    requires condition.len() == arr.len(),
    ensures
        /* Each element in result comes from arr at a position where condition is true */
        forall|k: int| 0 <= k < result@.len() ==>
            exists|i: int| 0 <= i < arr@.len() && condition@[i] == true && #[trigger] result@[k] == arr@[i],
        /* Every True position in condition contributes exactly one element to the result */
        forall|i: int| 0 <= i < condition@.len() && condition@[i] == true ==>
            exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and collect elements where condition is true using int-based prefix_true_count */
    let n: usize = condition.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res@.len() == prefix_true_count(condition, i as int),
            forall|k: int| 0 <= k && k < res@.len() ==> exists|j: int| 0 <= j && j < i as int && condition@[j] == true && #[trigger] res@[k] == arr@[j],
            forall|j: int| 0 <= j && j < i as int && condition@[j] == true ==> exists|k: int| 0 <= k && k < res@.len() && #[trigger] res@[k] == arr@[j],
        decreases n - i
    {
        match condition.get(i) {
            Some(&true) => {
                match arr.get(i) {
                    Some(&v) => {
                        res.push(v);
                        proof {
                            assert(res@.len() == prefix_true_count(condition, (i as int) + 1));
                            assert(forall|k: int| 0 <= k && k < res@.len() ==> exists|j: int| 0 <= j && j < (i as int) + 1 && condition@[j] == true && #[trigger] res@[k] == arr@[j]);
                            assert(forall|j: int| 0 <= j && j < (i as int) + 1 && condition@[j] == true ==> exists|k: int| 0 <= k && k < res@.len() && #[trigger] res@[k] == arr@[j]);
                        }
                    }
                    None => (),
                }
            }
            _ => (),
        }
        i = i + 1;
    }
    res
}

// </vc-code>


}
fn main() {}