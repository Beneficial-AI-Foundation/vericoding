// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper proofs for key properties */
exec fn contains(v: &Vec<i32>, val: i32) -> (result: bool)
    ensures result == (exists|i: int| 0 <= i < v.len() && v[i] == val)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v[j] != val
        decreases v.len() - i
    {
        if v[i] == val {
            return true;
        }
        i += 1;
    }
    false
}

spec fn all_distinct(v: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] != v[j]
}

spec fn is_subset_of(result: &Vec<i32>, s: &Vec<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] result[i]
}

spec fn covers_all(result: &Vec<i32>, s: &Vec<i32>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i]
}

proof fn push_maintains_subset(result: &Vec<i32>, s: &Vec<i32>, val: i32)
    requires is_subset_of(result, s), exists|j: int| 0 <= j < s.len() && s[j] == val
    ensures is_subset_of(&result.push(val), s)
{
}

proof fn push_extends_coverage(result: &Vec<i32>, s: &Vec<i32>, val: i32, covered_up_to: int)
    requires 
        forall|j: int| 0 <= j < covered_up_to ==> exists|k: int| 0 <= k < result.len() && result[k] == s[j],
        0 <= covered_up_to < s.len(),
        s[covered_up_to] == val
    ensures
        forall|j: int| 0 <= j <= covered_up_to ==> exists|k: int| 0 <= k < result.push(val).len() && result.push(val)[k] == s[j]
{
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
    /* code modified by LLM (iteration 5): added proof blocks to establish postconditions */
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            all_distinct(&result),
            is_subset_of(&result, s),
            forall|j: int| 0 <= j < i ==> exists|k: int| 0 <= k < result.len() && result[k] == #[trigger] s[j]
        decreases s.len() - i
    {
        if !contains(&result, s[i]) {
            proof {
                push_maintains_subset(&result, s, s[i]);
                push_extends_coverage(&result, s, s[i], i);
            }
            result.push(s[i]);
        }
        i += 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < s.len() ==> exists|k: int| 0 <= k < result.len() && result[k] == s[j]);
        assert(forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < s.len() && s[j] == result[k]);
    }
    
    result
}
// </vc-code>

}
fn main() {}