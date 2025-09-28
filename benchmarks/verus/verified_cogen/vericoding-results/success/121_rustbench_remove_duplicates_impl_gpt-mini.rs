// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): chooses the first index of x in sequence a */
spec fn first_index(a: Seq<i32>, x: i32) -> int { choose |i: int| 0 <= i < a.len() && a[i] == x && forall|j: int| 0 <= j < i ==> a[j] != x }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() >= 1,
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use sequence view res@ and a@ for spec-level indexing and adjust invariants */
    let mut res: Vec<i32> = Vec::new();
    let n: usize = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            forall|u: int| 0 <= u < (res.len() as int) ==> in_array(a@, res@[u]),
            forall|u: int, v: int| 0 <= u < v < (res.len() as int) ==> res@[u] != res@[v],
        decreases
            n - i
    {
        let mut k: usize = 0;
        let mut found: bool = false;
        while k < res.len()
            invariant
                0 <= k as int <= (res.len() as int),
                found == (exists|t: int| 0 <= t < k as int && res@[t] == a@[i as int]),
            decreases
                res.len() - k
        {
            if res[k] == a[i] {
                found = true;
                break;
            }
            k = k + 1;
        }
        if !found {
            res.push(a[i]);
        }
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}