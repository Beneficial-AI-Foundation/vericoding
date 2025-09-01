use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
spec fn multiset_equal(seq1: Seq<i32>, seq2: Seq<i32>) -> bool {
    multiset_count(seq1, |x: i32| true) =~= multiset_count(seq2, |x: i32| true)
}

spec fn multiset_count(seq: Seq<i32>, f: FnSpec(i32) -> bool) -> nat
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        let count_rest = multiset_count(seq.subrange(1, seq.len() as int), f);
        if f(seq[0]) {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

proof fn lemma_multiset_equal_commutative(seq1: Seq<i32>, seq2: Seq<i32>)
    ensures
        multiset_equal(seq1, seq2) == multiset_equal(seq2, seq1),
{
}

proof fn lemma_multiset_equal_reflexive(seq: Seq<i32>)
    ensures
        multiset_equal(seq, seq),
{
}

proof fn lemma_multiset_equal_transitive(seq1: Seq<i32>, seq2: Seq<i32>, seq3: Seq<i32>)
    ensures
        multiset_equal(seq1, seq2) && multiset_equal(seq2, seq3) ==> multiset_equal(seq1, seq3),
{
}

proof fn lemma_multiset_count_append(seq1: Seq<i32>, seq2: Seq<i32>, f: FnSpec(i32) -> bool)
    ensures
        multiset_count(seq1.add(seq2), f) == multiset_count(seq1, f) + multiset_count(seq2, f),
    decreases seq1.len(),
{
    if seq1.len() == 0 {
    } else {
        lemma_multiset_count_append(seq1.subrange(1, seq1.len() as int), seq2, f);
    }
}

spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

proof fn lemma_sorted_permutation_preserves_sorted(seq1: Seq<i32>, seq2: Seq<i32>)
    requires
        sorted(seq1),
        multiset_equal(seq1, seq2),
        sorted(seq2),
    ensures
        seq1 =~= seq2,
{
}
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        s@.len() == ret@.len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut ret = s.clone();
    let n = ret.len();
    
    proof {
        lemma_multiset_equal_reflexive(s@);
    }
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            s@.len() == ret@.len(),
            multiset_equal(s@, ret@),
        decreases n - i,
    {
        let mut j = 0;
        while j < n - i - 1
            invariant
                j <= n - i - 1,
                s@.len() == ret@.len(),
                multiset_equal(s@, ret@),
            decreases n - i - 1 - j,
        {
            if ret[j] > ret[j + 1] {
                let temp = ret[j];
                ret[j] = ret[j + 1];
                ret[j + 1] = temp;
                
                proof {
                    lemma_multiset_equal_commutative(s@, ret@);
                }
            }
            j += 1;
        }
        i += 1;
    }
    
    proof {
        lemma_sorted_permutation_preserves_sorted(s@, ret@);
    }
    
    ret
}
// </vc-code>

fn main() {}
}