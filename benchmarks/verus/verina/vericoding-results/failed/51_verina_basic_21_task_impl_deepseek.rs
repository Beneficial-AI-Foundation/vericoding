// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove duplicate definition of is_subseq_at and keep only necessary helpers */
proof fn subseq_transitive_lemma(sub: Vec<i32>, main: Vec<i32>, i: int, j: int, k: int)
    requires
        i <= j <= k,
        j - i >= sub.len() <= k - j,
        is_subseq_at(sub, main, i),
    ensures
        is_subseq_at(sub, main, j),
{
    assert(0 <= j && j + sub.len() <= main.len());
    assert forall|idx: int| 0 <= idx < sub.len() implies sub[idx] == main[j + idx] by {
        assert(sub[idx] == main[i + idx]);
        assert(main[i + idx] == main[j + idx]);
    };
}

proof fn subseq_reflexive_lemma(sub: Vec<i32>, i: int, len: int)
    requires
        0 <= i <= sub.len() - len,
        len >= 0,
    ensures
        is_subseq_at(Vec::from_seq(sub.subrange(i, i + len)), sub, i),
{
    assert(0 <= i && i + len <= sub.len());
    assert forall|j: int| 0 <= j < len implies sub.subrange(i, i + len)[j] == sub[i + j] by {
        assert(sub.subrange(i, i + len)[j] == sub[i + j]);
    };
}

proof fn subseq_concat_lemma(seq1: Vec<i32>, seq2: Vec<i32>, main: Vec<i32>, pos1: int, pos2: int)
    requires
        is_subseq_at(seq1, main, pos1),
        is_subseq_at(seq2, main, pos2),
        pos1 + seq1.len() <= pos2,
    ensures
        is_subseq_at(Vec::from_seq(seq1@.add(seq2@)), main, pos1),
{
    assert(0 <= pos1 && pos1 + seq1.len() + seq2.len() <= main.len());
    assert forall|j: int| 0 <= j < seq1.len() implies seq1@.add(seq2@)[j] == main[pos1 + j] by {
        assert(seq1@.add(seq2@)[j] == seq1@[j]);
        assert(seq1@[j] == main[pos1 + j]);
    };
    assert forall|j: int| seq1.len() <= j < seq1.len() + seq2.len() implies seq1@.add(seq2@)[j] == main[pos1 + j] by {
        assert(seq1@.add(seq2@)[j] == seq2@[j - seq1.len()]);
        assert(seq2@[j - seq1.len()] == main[pos2 + (j - seq1.len())]);
        assert(main[pos2 + (j - seq1.len())] == main[pos1 + j]);
    };
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implementation with proper verification */
{
    if sub.is_empty() {
        return true;
    }
    if main.is_empty() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= main.len() - sub.len() {
        invariant i <= main.len() - sub.len() + 1;
        decreases main.len() - i;
        
        let mut j: usize = 0;
        let mut found = true;
        
        while j < sub.len() {
            invariant j <= sub.len();
            decreases sub.len() - j;
            
            if main[i + j] != sub[j] {
                found = false;
                break;
            }
            j += 1;
        }
        
        if found {
            assert(i >= 0 && i + sub.len() <= main.len());
            assert(forall|idx: int| 0 <= idx < sub.len() ==> sub[idx] == main[i + idx]);
            assert(is_subseq_at(*sub, *main, i as int));
            return true;
        }
        i += 1;
    }
    
    assert(!exists|k: int| is_subseq_at(*sub, *main, k));
    false
}
// </vc-code>

}
fn main() {}