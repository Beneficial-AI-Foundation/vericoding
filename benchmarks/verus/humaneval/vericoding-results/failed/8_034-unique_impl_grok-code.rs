// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation by using nat for indices, Vec[i as usize] for Vec indexing instead of Seq@[i], and casting to int in invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < s.len() as nat
        invariant
            0 <= i as int <= s.len() as int,
            forall|k: int, l: int| 0 <= k < l < result@.len() as int ==> result@[k] < result@[l],
            forall|k: int| #![auto] 0 <= k < result@.len() as int ==> s@.contains(result@[k]),
            forall|k: int| 0 <= k < i as int ==> result@.contains(s@[k]),
        decreases (s.len() as int) - (i as int)
    {
        let val = s[i as usize];
        let mut j: nat = 0;
        let mut found = false;
        while j < result.len() as nat
            invariant
                0 <= j as int <= result@.len() as int,
                found == (exists|l: int| 0 <= l < j as int ==> result@[l] == val),
        {
            if result[j as usize] == val {
                found = true;
                break;
            }
            j = j + 1;
        }
        if !found {
            let mut k: nat = 0;
            while k < result.len() as nat && result[k as usize] < val
                invariant
                    0 <= k as int <= result@.len() as int,
                    forall|m: int| 0 <= m < k as int ==> result@[m] < val,
            {
                k = k + 1;
            }
            result.insert(k as usize, val);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}