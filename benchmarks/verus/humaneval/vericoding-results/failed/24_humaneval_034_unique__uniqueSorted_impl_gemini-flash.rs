// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fix int/ghost context errors by using `as nat` for indexing where applicable. */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() <= i,
            forall|k: int, l: int| 0 <= k < l < result@.len() ==> result@[k] < result@[l],
            forall|x: i8| result@.contains(x) ==> s@.contains(x),
            forall|idx: int| 0 <= idx < i && !result@.contains(s@[idx]) ==> (
                result@.len() > 0 && s@[idx] <= result@[result@.len() - 1 as int] && s@[idx] != result@[result@.len() - 1 as int]
                ||
                (result@.len() == 0 && s@[idx] != s@[0])
            ),
            forall|x: i8| (
                s@.contains(x) &&
                (result@.len() == 0 || x > result@[(result.len() - 1) as int]) &&
                ( i as int == s@.len() || x < s@[i as int] )
            ) ==> !result@.contains(x),
            forall|x: i8| (
                s@.contains(x) && x < s@[0]
            )==> !result@.contains(x),
        decreases s.len() - i
    {
        let val = s@[i as nat];
        if result.is_empty() || result@[(result.len() - 1) as nat] < val {
            result.push(val);
        }

        proof {
            if i < s.len() {
                if result.is_empty() || result@[(result.len() - 1) as nat] < val {
                    assert(s@.contains(val));
                }
                if result.len() > 1 {
                    let last_idx: int = (result.len() - 2) as int;
                    assert(result@[last_idx as nat] < result@[(last_idx + 1) as nat]);
                }
            }
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}