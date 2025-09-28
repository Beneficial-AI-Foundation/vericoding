// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_is_subseq_at_unmatched_witness(sub: Vec<i32>, main: Vec<i32>, i: int, j: int)
    requires
        0 <= i,
        i + sub.len() <= main.len(),
        0 <= j < sub.len(),
        sub[j] != main[i + j],
    ensures
        !is_subseq_at(sub, main, i),
{
    assert(!(forall|k: int| 0 <= k < sub.len() ==> sub[k] == main[i + k]));
}

proof fn lemma_is_subseq_at_matched(sub: Vec<i32>, main: Vec<i32>, i: int)
    requires
        0 <= i,
        i + sub.len() <= main.len(),
        forall|k: int| 0 <= k < sub.len() ==> sub[k] == main[i + k],
    ensures
        is_subseq_at(sub, main, i),
{
}

/* helper modified by LLM (iteration 2): added decreases clause to while loop */
fn check_match_at_i(sub: &Vec<i32>, main: &Vec<i32>, i: usize) -> (is_match: bool)
    requires
        sub.len() > 0,
        i + sub.len() <= main.len(),
    ensures
        is_match <==> is_subseq_at(*sub, *main, i as int),
{
    let sub_len = sub.len();
    let mut j: usize = 0;
    while j < sub_len
        invariant
            sub.len() > 0,
            i + sub.len() <= main.len(),
            0 <= j <= sub.len(),
            forall|k: int| 0 <= k < j ==> sub[k] == main[i + k],
        decreases sub_len - j
    {
        if main[i + j] != sub[j] {
            proof {
                lemma_is_subseq_at_unmatched_witness(*sub, *main, i as int, j as int);
            }
            return false;
        }
        j = j + 1;
    }
    proof {
        lemma_is_subseq_at_matched(*sub, *main, i as int);
    }
    return true;
}

proof fn lemma_is_subseq_at_impossible_length(sub: Vec<i32>, main: Vec<i32>, i: int)
    requires
        main.len() < i + sub.len(),
        0 <= i,
    ensures !is_subseq_at(sub, main, i)
{}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to the main loop */
    let sub_len = sub.len();
    let main_len = main.len();

    if sub_len == 0 {
        proof {
            assert(is_subseq_at(*sub, *main, 0));
        }
        return true;
    }

    if sub_len > main_len {
        proof {
            assert forall|i: int| !is_subseq_at(*sub, *main, i) by {
                if i < 0 {
                    assert(!is_subseq_at(*sub, *main, i));
                } else {
                    lemma_is_subseq_at_impossible_length(*sub, *main, i);
                    assert(!is_subseq_at(*sub, *main, i));
                }
            }
        }
        return false;
    }

    let mut i: usize = 0;
    while i <= main_len - sub_len
        invariant
            0 < sub.len() <= main.len(),
            0 <= i <= main_len - sub.len() + 1,
            forall|k: int| 0 <= k < i ==> !is_subseq_at(*sub, *main, k),
        decreases (main_len - sub_len) - i
    {
        if check_match_at_i(sub, main, i) {
            assert(is_subseq_at(*sub, *main, i as int));
            return true;
        } else {
            assert(!is_subseq_at(*sub, *main, i as int));
        }
        i = i + 1;
    }

    proof {
        assert forall|k: int| !is_subseq_at(*sub, *main, k) by {
            if k < 0 {
                assert(!is_subseq_at(*sub, *main, k));
            } else if (k as usize) <= main_len - sub_len {
                // This range is covered by the loop invariant
            } else {
                lemma_is_subseq_at_impossible_length(*sub, *main, k);
                assert(!is_subseq_at(*sub, *main, k));
            }
        }
    }
    return false;
}
// </vc-code>

}
fn main() {}