// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): non-negativity of count_true */
proof fn count_true_nonneg(condition: Seq<bool>) ensures count_true(condition) >= 0 decreases condition.len() {
    if condition.len() == 0 {
    } else {
        count_true_nonneg(condition.skip(1));
    }
}

/* helper modified by LLM (iteration 5): split count_true into prefix and suffix */
proof fn count_true_split(condition: Seq<bool>, i: int)
    requires 0 <= i && i <= condition.len()
    ensures count_true(condition) == count_true(condition[..i]) + count_true(condition.skip(i))
    decreases condition.len()
{
    if i == 0 {
    } else {
        let rest = condition.skip(1);
        count_true_split(rest, i - 1);
        assert(count_true(condition) == (if condition[0] { 1 } else { 0 }) + count_true(rest));
        assert(count_true(condition[..i]) == (if condition[0] { 1 } else { 0 }) + count_true(rest[..(i - 1)]));
        assert(count_true(condition.skip(i)) == count_true(rest.skip(i - 1)));
        assert(count_true(condition) == count_true(condition[..i]) + count_true(condition.skip(i)));
    }
}

/* helper modified by LLM (iteration 5): count_true on empty suffix is zero */
proof fn count_true_skip_empty(condition: Seq<bool>)
    ensures count_true(condition.skip(condition.len())) == 0
    decreases condition.len()
{
    count_true_split(condition, condition.len());
    assert(condition[..condition.len()] == condition);
    assert(count_true(condition[..condition.len()]) == count_true(condition));
    assert(count_true(condition) == count_true(condition) + count_true(condition.skip(condition.len())));
    assert(count_true(condition.skip(condition.len())) == 0);
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
    /* code modified by LLM (iteration 5): implement compress using additive invariant to avoid subtraction and prove final length */
    let n = condition.len();
    let mut i: int = 0;
    let mut result = Vec::<f32>::new();
    let mut mapping = Vec::<int>::new();

    while i < n
        invariant 0 <= i && i <= n
        invariant mapping@.len() + count_true(condition@.skip(i)) == count_true(condition@)
        invariant result@.len() == mapping@.len()
        invariant forall|k: int| 0 <= k < mapping@.len() ==> 0 <= mapping@[k] < i
        invariant forall|k: int| 0 <= k < mapping@.len() ==> condition@[mapping@[k]] == true
        invariant forall|p: int, q: int| 0 <= p < q < mapping@.len() ==> mapping@[p] < mapping@[q]
        invariant forall|k: int| 0 <= k < mapping@.len() ==> result@[k] == a@[mapping@[k]]
        decreases n - i
    {
        if condition@[i] {
            result.push(a@[i]);
            mapping.push(i);
        }
        i += 1;
    }

    proof {
        let mapping_seq = mapping@;
        assert(mapping_seq.len() + count_true(condition@.skip(n)) == count_true(condition@));
        count_true_skip_empty(condition@);
        assert(count_true(condition@.skip(n)) == 0);
        assert(mapping_seq.len() == count_true(condition@));
        assert(result@.len() == mapping_seq.len());
        assert(forall|k: int| 0 <= k < mapping_seq.len() ==> 0 <= mapping@[k] < n);
        assert(forall|k: int| 0 <= k < mapping_seq.len() ==> condition@[mapping@[k]] == true);
        assert(forall|k: int| 0 <= k < result@.len() ==> result@[k] == a@[mapping@[k]]);
        assert(forall|i: int, j: int| 0 <= i < j < mapping_seq.len() ==> mapping@[i] < mapping@[j]);
    }

    result
}

// </vc-code>

}
fn main() {}