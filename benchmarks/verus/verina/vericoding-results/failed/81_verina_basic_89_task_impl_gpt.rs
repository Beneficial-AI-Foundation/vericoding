// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): refine triggers and invariants for quantifiers to cover all variables */
spec fn contains(v: &Vec<i32>, x: i32) -> bool {
    exists|j: int| 0 <= j < v.len() && #[trigger] (v@)[j] == x
}

fn contains_exec(v: &Vec<i32>, x: i32) -> (b: bool)
    ensures
        b == contains(v, x)
{
    let mut j: usize = 0;
    let mut found: bool = false;
    while j < v.len()
        invariant
            0 <= j as int <= v.len(),
            found ==> exists|k: int| 0 <= k < j as int && #[trigger] (v@)[k] == x,
            !found ==> forall|k: int| 0 <= k < j as int ==> #[trigger] (v@)[k] != x,
        decreases v.len() - j as int
    {
        if v[j] == x {
            found = true;
        }
        j += 1;
    }
    proof {
        if found {
            assert(exists|k: int| 0 <= k < j as int && (v@)[k] == x);
        } else {
            assert(forall|k: int| 0 <= k < v.len() ==> (v@)[k] != x);
        }
    }
    found
}
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
    /* code modified by LLM (iteration 4): fix trigger coverage and invariant bounds; allow k < i+1 and guard with k < s.len() */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i as int <= s.len(),
            forall|a: int, b: int|
                0 <= a < b < result.len() ==> #[trigger] (result@)[a] != #[trigger] (result@)[b],
            forall|rj: int|
                0 <= rj < result.len() ==>
                    exists|k: int| 0 <= k < s.len() && k < i as int + 1 && s[k] == #[trigger] (result@)[rj],
            forall|k: int|
                0 <= k < i as int ==> exists|rj: int| 0 <= rj < result.len() && #[trigger] (result@)[rj] == #[trigger] s[k],
        decreases s.len() - i as int
    {
        let x = s[i];
        let in_res = contains_exec(&result, x);
        if !in_res {
            let old_len = result.len();
            proof {
                assert(!contains(&result, x));
                assert(forall|a: int| 0 <= a < old_len ==> (result@)[a] != x);
            }
            result.push(x);
            proof {
                assert((result@)[old_len as int] == x);
                // New element distinct from all previous
                assert(forall|a: int| 0 <= a < old_len ==> (result@)[a] != (result@)[old_len as int]);
                // Coverage: witness k = i for the new element (note i < s.len() by loop condition)
                assert(i < s.len());
                assert(exists|k: int| k == i as int && 0 <= k < s.len() && k < i as int + 1 && s[k] == (result@)[old_len as int]);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}