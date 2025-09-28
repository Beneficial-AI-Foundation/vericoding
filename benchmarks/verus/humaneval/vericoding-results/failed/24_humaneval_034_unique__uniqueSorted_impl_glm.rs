// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed problematic invariant and find_index function */
fn remove_duplicates(s: Vec<i8>) -> (result: Vec<i8>)
    requires
        forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] <= s@[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
        forall|x: i8| result@.contains(x) ==> s@.contains(x),
        forall|x: i8| s@.contains(x) ==> result@.contains(x),
{
    if s.len() == 0 {
        Vec::new()
    } else {
        let mut result = Vec::new();
        result.push(s[0]);
        let mut i = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                result.len() >= 1,
                result[0] == s[0],
                forall|k: int| 0 <= k < result.len() - 1 ==> result[k] < result[k + 1],
                forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < i && s[j] == result[k],
                forall|j: int| 0 <= j < i ==> exists|k: int| 0 <= k < result.len() && result[k] == s[j],
            decreases s.len() - i
        {
            if s[i] != result[result.len() - 1] {
                result.push(s[i]);
            }
            i += 1;
        }
        proof {
            assert forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j] by {
                let k = i;
                let l = j;
                if k + 1 < l {
                    assert(result@[k] < result@[k + 1]);
                    assert(result@[k + 1] < result@[l]);
                }
            }
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn unique_sorted(s: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] <= s@[j],
    ensures 
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
        forall|x: i8| result@.contains(x) ==> s@.contains(x),
        forall|x: i8| s@.contains(x) ==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Removed call to find_index and fixed invariant */
    remove_duplicates(s)
}
// </vc-code>


}

fn main() {}