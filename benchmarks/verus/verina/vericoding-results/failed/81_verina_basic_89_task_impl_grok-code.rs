// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn contains(v: &Vec<i32>, x: i32) -> (res: bool)
    ensures
        res <==> exists|i: int| 0 <= i < v.len() && #[trigger] v[i] == x
{
    let mut i = 0;
    while i < v.len()
        invariant
            forall|j: int| 0 <= j < i ==> v[j] != x,
            0 <= i <= v.len()
        decreases v.len() - i
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
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
/* code modified by LLM (iteration 5): Added invariant that every element in result came from s up to i */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] != result[q],
            forall|k: int| #![trigger s[k]] 0 <= k < i ==> exists|j: int| 0 <= j < result.len() && result[j] == s[k],
            forall|p: int| 0 <= p < result.len() ==> exists|q: int| 0 <= q < i && s[q] == result[p]
        decreases s.len() - i
    {
        let is_present = contains(&result, s[i]);
        if !is_present {
            result.push(s[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}