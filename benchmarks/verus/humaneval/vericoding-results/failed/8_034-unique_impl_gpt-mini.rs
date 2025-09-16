// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): wrapper for sequence contains */
spec fn contains_i32(s: Vec<i32>, x: i32) -> bool { s@.contains(x) }
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
    /* code modified by LLM (iteration 5): avoid using Vec::contains by manual linear search */
    let mut uniques: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|x: i32| (exists|k: int| 0 <= k < (i as int) && s@[k] == x) ==> uniques@.contains(x),
            forall|p: int, q: int| 0 <= p < q < (uniques.len() as int) ==> uniques@[p] != uniques@[q],
        decreases s.len() - i
    {
        let x: i32 = s[i];
        let mut found: bool = false;
        let mut k: usize = 0;
        while k < uniques.len()
            invariant
                k <= uniques.len(),
                (found ==> (exists|t: int| 0 <= t < (k as int) && uniques@[t] == x)),
            decreases uniques.len() - k
        {
            if uniques[k] == x {
                found = true;
            }
            k = k + 1;
        }
        if !found {
            uniques.push(x);
        }
        i = i + 1;
    }

    let mut result: Vec<i32> = Vec::new();
    while uniques.len() > 0
        invariant
            forall|k: int| 0 <= k < (result.len() as int) ==> s@.contains(result@[k]),
            forall|x: i32| (exists|t: int| 0 <= t < (s.len() as int) && s@[t] == x) ==> result@.contains(x) || uniques@.contains(x),
            forall|a: int, b: int| 0 <= a < (result.len() as int) && 0 <= b < (uniques.len() as int) ==> result@[a] < uniques@[b],
        decreases uniques.len()
    {
        let mut min_idx: usize = 0;
        let mut j: usize = 1;
        while j < uniques.len()
            invariant
                min_idx < uniques.len(),
                j <= uniques.len(),
                forall|t: int| 0 <= t < (j as int) ==> uniques@[(min_idx as int)] <= uniques@[t],
            decreases uniques.len() - j
        {
            if uniques[j] < uniques[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        let m: i32 = uniques[min_idx];
        result.push(m);
        uniques.remove(min_idx);
    }
    result
}
// </vc-code>

}
fn main() {}