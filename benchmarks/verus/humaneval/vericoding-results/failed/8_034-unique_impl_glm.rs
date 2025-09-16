// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>
fn contains_unique(seq: Seq<i32>, value: i32) -> bool {
    seq.contains(value) && seq.count_of(value) == 1
}

proof fn lemma_contains_after_insert(mut seq: Seq<i32>, i: int, value: i32)
    requires
        0 <= i <= seq.len(),
        !seq.contains(value),
    ensures
        contains_unique(seq.insert(i, value), value),
{
    assert(seq.insert(i, value).contains(value));
    assert(seq.insert(i, value).count_of(value) == 1);
}

proof fn lemma_unique_elements_preserved(seq: Seq<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j],
{
    let mut i: int = 0;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            forall|a: int, b: int| 0 <= a < b < i ==> seq[a] != seq[b],
        decreases seq.len() - i
    {
        let mut j: int = 0;
        while j < i
            invariant
                0 <= j <= i,
                0 <= i < seq.len(),
                forall|a: int, b: int| 0 <= a < b < i ==> (a != j && b != j ==> seq[a] != seq[b]),
                forall|k: int| 0 <= k < j ==> seq[k] != seq[j],
            decreases i - j
        {
            assert(seq[j] != seq[i]);
            j += 1;
        }
        i += 1;
    }
}
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
    /* code modified by LLM (iteration 2): added missing braces for function body */
    let mut result: Vec<i32> = Vec::new();
    let mut seen: Set<i32> = Set::empty();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b],
            forall|j: int| 0 <= j < result.len() ==> seen.contains(result[j]),
            forall|j: int| 0 <= j < i ==> s@[j] == result@[j],
            forall|j: int| 0 <= j < result.len() ==> s@.contains(result[j]),
        decreases s.len() - i
    {
        if i == 0 {
            result.push(s[i]);
            seen.insert(s[i]);
        } else {
            if !seen.contains(s[i]) {
                let mut insert_pos: usize = 0;
                while insert_pos < result.len()
                    invariant
                        0 <= insert_pos <= result.len(),
                        forall|a: int, b: int| 0 <= a < b < insert_pos ==> result[a] < result[b],
                        forall|a: int, b: int| insert_pos <= a < b < result.len() ==> result[a] < result[b],
                        forall|k: int| 0 <= k < insert_pos ==> result[k] < s[i],
                        forall|k: int| insert_pos <= k < result.len() ==> s[i] < result[k],
                    decreases result.len() - insert_pos
                {
                    if s[i] < result[insert_pos] {
                        break;
                    }
                    insert_pos += 1;
                }
                result.insert(insert_pos, s[i]);
                seen.insert(s[i]);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}