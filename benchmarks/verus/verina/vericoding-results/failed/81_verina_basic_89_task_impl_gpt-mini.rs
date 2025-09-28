// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): index identity helper */
spec fn idx(i: int) -> int { i }

/* helper modified by LLM (iteration 5): i32 trigger wrapper */
spec fn val_i32(x: i32) -> i32 { x }
// </vc-helpers>

// <vc-spec>
fn set_to_seq(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],

        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] result[i],

        forall|i: int| 0 <= i < s.len() ==> 
            exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build sequence of unique elements using trigger wrapper */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            forall|a: int, b: int| 0 <= a < b < (res.len() as int) ==> res[idx(a)] != res[idx(b)],
            forall|r: int| 0 <= r < (res.len() as int) ==> exists|j: int| 0 <= j < (i as int) && s[idx(j)] == #[trigger] val_i32(res[idx(r)]),
            forall|k: int| 0 <= k < (i as int) ==> exists|j: int| 0 <= j < (res.len() as int) && res[idx(j)] == #[trigger] val_i32(s[idx(k)]),
        decreases s.len() - i
    {
        let x = s[i];
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < res.len()
            invariant
                forall|a: int, b: int| 0 <= a < b < (res.len() as int) ==> res[idx(a)] != res[idx(b)],
                (found ==> exists|p: int| 0 <= p < (j as int) && res[idx(p)] == #[trigger] val_i32(x)),
                (!found ==> forall|p: int| 0 <= p < (j as int) ==> res[idx(p)] != #[trigger] val_i32(x)),
            decreases res.len() - j
        {
            if res[j] == x {
                found = true;
            }
            j += 1;
        }
        if !found {
            res.push(x);
        }
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}