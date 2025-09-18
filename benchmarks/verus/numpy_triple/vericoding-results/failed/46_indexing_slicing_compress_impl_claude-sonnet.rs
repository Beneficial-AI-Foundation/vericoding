// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed count_true_prefix to match count_true recursion pattern */
spec fn count_true_prefix(condition: Seq<bool>, len: int) -> int
    decreases len
{
    if len <= 0 {
        0
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true_prefix(condition.skip(1), len - 1)
    }
}

proof fn count_true_prefix_eq(condition: Seq<bool>)
    ensures count_true_prefix(condition, condition.len() as int) == count_true(condition)
    decreases condition.len()
{
    if condition.len() == 0 {
    } else {
        count_true_prefix_eq(condition.skip(1));
    }
}

proof fn count_true_incremental(condition: Seq<bool>, idx: int)
    requires 0 <= idx < condition.len()
    ensures count_true_prefix(condition, idx + 1) == 
            count_true_prefix(condition, idx) + (if condition[idx] { 1int } else { 0int })
    decreases condition.len() - idx
{
}

proof fn mapping_exists_lemma(condition: Seq<bool>, result: Seq<f32>, mapping: Seq<usize>, a: Seq<f32>)
    requires
        result.len() == mapping.len(),
        forall|i: int| 0 <= i < mapping.len() ==> 
            0 <= mapping[i] < condition.len() &&
            condition[mapping[i] as int] == true,
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == a[mapping[i] as int],
        forall|i: int, j: int| 0 <= i < j < mapping.len() ==> 
            mapping[i] < mapping[j]
    ensures
        exists|int_mapping: Seq<int>|
            int_mapping.len() == result.len() &&
            (forall|i: int| 0 <= i < int_mapping.len() ==> 
                0 <= int_mapping[i] < condition.len() &&
                condition[int_mapping[i]] == true) &&
            (forall|i: int| 0 <= i < result.len() ==> 
                result[i] == a[int_mapping[i]]) &&
            (forall|i: int, j: int| 0 <= i < j < int_mapping.len() ==> 
                int_mapping[i] < int_mapping[j])
{
}
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int
    decreases condition.len()
{
    if condition.len() == 0 {
        0
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn compress(condition: Vec<bool>, a: Vec<f32>) -> (result: Vec<f32>)
    requires condition.len() == a.len(),
    ensures
        result.len() == count_true(condition@),
        exists|mapping: Seq<int>|
            mapping.len() == result.len() &&
            (forall|i: int| 0 <= i < mapping.len() ==> 
                0 <= mapping[i] < condition.len() &&
                condition@[mapping[i]] == true) &&
            (forall|i: int| 0 <= i < result.len() ==> 
                result@[i] == a@[mapping[i]]) &&
            (forall|i: int, j: int| 0 <= i < j < mapping.len() ==> 
                mapping[i] < mapping[j]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed mapping bounds and added witness for postcondition */
    let mut result = Vec::new();
    let mut mapping = Vec::<usize>::new();
    let mut idx = 0;
    
    while idx < condition.len()
        invariant
            0 <= idx <= condition.len(),
            result.len() == mapping.len(),
            result.len() <= count_true(condition@),
            forall|i: int| 0 <= i < mapping.len() ==> 
                0 <= mapping@[i] < condition.len() &&
                mapping@[i] < idx &&
                condition@[mapping@[i] as int] == true,
            forall|i: int| 0 <= i < result.len() ==> 
                0 <= mapping@[i] < a.len() &&
                result@[i] == a@[mapping@[i] as int],
            forall|i: int, j: int| 0 <= i < j < mapping.len() ==> 
                mapping@[i] < mapping@[j],
        decreases condition.len() - idx
    {
        if condition[idx] {
            proof {
                assert(idx < a.len());
            }
            result.push(a[idx]);
            mapping.push(idx);
        }
        idx += 1;
    }
    
    proof {
        assert(result.len() == count_true(condition@));
        
        let int_mapping = mapping@.map(|i, val: usize| val as int);
        assert(int_mapping.len() == result.len());
        
        mapping_exists_lemma(condition@, result@, mapping@, a@);
    }
    
    result
}
// </vc-code>

}
fn main() {}