// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
spec fn contains_element(seq: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == x
}

spec fn all_distinct(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
}

proof fn lemma_contains_preserved(a: Seq<i32>, result: Seq<i32>, x: i32)
    requires
        forall|k: int| 0 <= k < result.len() ==> contains_element(a, result[k]),
        contains_element(result, x),
    ensures
        contains_element(a, x),
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to all loops */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> in_array(a@, result[k]) && !in_array(b@, result[k]),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] != result[y],
        decreases a.len() - i
    {
        let element = a[i];
        let mut found_in_b = false;
        let mut j = 0;
        
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                found_in_b == exists|k: int| 0 <= k < j && b[k] == element,
            decreases b.len() - j
        {
            if b[j] == element {
                found_in_b = true;
            }
            j += 1;
        }
        
        if !found_in_b {
            let mut already_in_result = false;
            let mut k = 0;
            
            while k < result.len()
                invariant
                    0 <= k <= result.len(),
                    already_in_result == exists|m: int| 0 <= m < k && result[m] == element,
                decreases result.len() - k
            {
                if result[k] == element {
                    already_in_result = true;
                }
                k += 1;
            }
            
            if !already_in_result {
                result.push(element);
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}