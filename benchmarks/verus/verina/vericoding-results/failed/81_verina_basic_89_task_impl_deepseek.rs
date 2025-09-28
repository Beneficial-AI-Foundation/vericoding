// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn distinct_seq(s: Seq<i32>) -> (result: Seq<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] result[i],
        forall|i: int| 0 <= i < s.len() ==> 
            exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i],
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let x = s[s.len() - 1];
        let rest = s.subrange(0, s.len() - 1);
        let result_rest = distinct_seq(rest);
        if exists|i: int| 0 <= i < result_rest.len() && result_rest[i] == x {
            result_rest
        } else {
            result_rest.push(x)
        }
    }
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
    /* code modified by LLM (iteration 5): Fixed trigger annotations for quantifiers */
    let mut result: Vec<i32> = Vec::new();
    let mut seen: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
            forall|k: int| 0 <= k < result.len() ==> 
                exists|m: int| 0 <= m < seen.len() && #[trigger] seen[m] == #[trigger] result[k],
            forall|m: int| 0 <= m < seen.len() ==> 
                exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] seen[m],
            forall|j: int| 0 <= j < i ==> 
                exists|m: int| 0 <= m < seen.len() && #[trigger] seen[m] == #[trigger] s[j],
        decreases s.len() - i,
    {
        let x = s[i];
        let mut found = false;
        let mut j: usize = 0;
        while j < seen.len()
            invariant
                j <= seen.len(),
                !found ==> forall|m: int| 0 <= m < j ==> seen[m] != x,
                found ==> exists|m: int| 0 <= m < j && #[trigger] seen[m] == x,
            decreases seen.len() - j,
        {
            if seen[j] == x {
                found = true;
                break;
            }
            j += 1;
        }
        if !found {
            result.push(x);
            seen.push(x);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}