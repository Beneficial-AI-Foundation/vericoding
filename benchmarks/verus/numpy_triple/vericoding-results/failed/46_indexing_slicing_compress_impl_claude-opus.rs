// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_true_take_push_true(s: Seq<bool>, i: int)
    requires 0 <= i < s.len(),
        s[i] == true,
    ensures count_true(s.take(i + 1)) == count_true(s.take(i)) + 1,
{
    /* helper modified by LLM (iteration 5): Fixed proof for count_true with take and push */
    let taken = s.take(i);
    let taken_plus = s.take(i + 1);
    assert(taken_plus.len() == i + 1);
    assert(taken.len() == i);
    assert(taken_plus == taken.push(s[i]));
    assert(s[i] == true);
    
    // Prove by induction on the structure
    if i == 0 {
        assert(taken.len() == 0);
        assert(count_true(taken) == 0);
        assert(taken_plus.len() == 1);
        assert(taken_plus[0] == s[0]);
        assert(s[0] == true);
        assert(count_true(taken_plus) == 1);
    } else {
        // For i > 0, we need to show the recursive structure
        assert(taken_plus[i] == s[i]);
        assert(s[i] == true);
    }
}

proof fn lemma_count_true_take_push_false(s: Seq<bool>, i: int)
    requires 0 <= i < s.len(),
        s[i] == false,
    ensures count_true(s.take(i + 1)) == count_true(s.take(i)),
{
    /* helper modified by LLM (iteration 5): Fixed proof for count_true with false element */
    let taken = s.take(i);
    let taken_plus = s.take(i + 1);
    assert(taken_plus == taken.push(s[i]));
    assert(s[i] == false);
}

proof fn lemma_count_true_empty()
    ensures count_true(Seq::<bool>::empty()) == 0,
{}
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
    /* code modified by LLM (iteration 5): Simplified proof structure to fix verification */
    let mut result = Vec::new();
    let ghost mut mapping: Seq<int> = Seq::empty();
    
    proof {
        lemma_count_true_empty();
        assert(count_true(condition@.take(0)) == 0);
        assert(result.len() == 0);
        assert(mapping.len() == 0);
    }
    
    let mut i = 0;
    while i < condition.len()
        invariant
            0 <= i <= condition.len(),
            condition.len() == a.len(),
            result.len() == count_true(condition@.take(i as int)),
            mapping.len() == result.len(),
            forall|j: int| 0 <= j < mapping.len() ==>
                0 <= mapping[j] < i &&
                condition@[mapping[j]] == true,
            forall|j: int| 0 <= j < result.len() ==>
                result@[j] == a@[mapping[j]],
            forall|j: int, k: int| 0 <= j < k < mapping.len() ==>
                mapping[j] < mapping[k],
        decreases condition.len() - i
    {
        if condition[i] {
            result.push(a[i]);
            proof {
                lemma_count_true_take_push_true(condition@, i as int);
                mapping = mapping.push(i as int);
                assert(mapping.len() == result.len());
                assert(condition@[i as int] == true);
                assert(mapping[mapping.len() - 1] == i);
                assert(result@[result.len() - 1] == a@[i as int]);
            }
        } else {
            proof {
                lemma_count_true_take_push_false(condition@, i as int);
            }
        }
        i += 1;
    }
    
    proof {
        assert(i == condition.len());
        assert(condition@.take(condition.len() as int) == condition@);
        assert(result.len() == count_true(condition@));
        assert(exists|m: Seq<int>| 
            m.len() == result.len() &&
            (forall|j: int| 0 <= j < m.len() ==>
                0 <= m[j] < condition.len() &&
                condition@[m[j]] == true) &&
            (forall|j: int| 0 <= j < result.len() ==>
                result@[j] == a@[m[j]]) &&
            (forall|j: int, k: int| 0 <= j < k < m.len() ==>
                m[j] < m[k])) by {
            assert(mapping.len() == result.len());
            assert(forall|j: int| 0 <= j < mapping.len() ==>
                0 <= mapping[j] < condition.len() &&
                condition@[mapping[j]] == true);
            assert(forall|j: int| 0 <= j < result.len() ==>
                result@[j] == a@[mapping[j]]);
            assert(forall|j: int, k: int| 0 <= j < k < mapping.len() ==>
                mapping[j] < mapping[k]);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}