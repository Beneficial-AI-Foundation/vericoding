// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added sequence equality lemma and bounds checking */
spec fn subrange_matches(main: Seq<i32>, sub: Seq<i32>, start: int) -> bool {
    start >= 0 && start + sub.len() <= main.len() && main.subrange(start, start + sub.len()) =~= sub
}

spec fn valid_search_range(main_len: int, sub_len: int, i: int) -> bool {
    0 <= i <= main_len - sub_len && i + sub_len <= main_len
}

proof fn seq_equality_lemma(main: Seq<i32>, sub: Seq<i32>, start: int)
    requires
        start >= 0,
        start + sub.len() <= main.len(),
        forall|idx: int| 0 <= idx < sub.len() ==> main[start + idx] == sub[idx],
    ensures
        main.subrange(start, start + sub.len()) =~= sub,
{
    let subseq = main.subrange(start, start + sub.len());
    assert(subseq.len() == sub.len());
    assert(forall|i: int| 0 <= i < sub.len() ==> subseq[i] == sub[i]);
}
// </vc-helpers>

// <vc-spec>
fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    requires
        sub.len() <= main.len(),

    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and proof construction */
    let main_len = main.len();
    let sub_len = sub.len();
    
    if sub_len == 0 {
        proof {
            assert(main@.subrange(0, 0) =~= sub@);
        }
        return true;
    }
    
    if main_len < sub_len {
        return false;
    }
    
    let mut i: usize = 0;
    let max_i = main_len - sub_len;
    
    while i <= max_i
        invariant
            0 <= i <= max_i + 1,
            max_i == main_len - sub_len,
            sub_len > 0,
            main_len >= sub_len,
            forall|k: int| 0 <= k < i ==> !subrange_matches(main@, sub@, k),
        decreases max_i + 1 - i
    {
        let mut j: usize = 0;
        let mut matches = true;
        
        while j < sub_len && matches
            invariant
                0 <= j <= sub_len,
                i <= max_i,
                i + sub_len <= main_len,
                i + j < main_len,
                matches ==> (forall|idx: int| 0 <= idx < j ==> main@[i + idx] == sub@[idx]),
            decreases sub_len - j
        {
            assert(i + j < main_len);
            assert(j < sub_len);
            if main[i + j] != sub[j] {
                matches = false;
            } else {
                j += 1;
            }
        }
        
        if matches && j == sub_len {
            proof {
                assert(i + sub_len <= main_len);
                assert(forall|idx: int| 0 <= idx < sub_len ==> main@[i + idx] == sub@[idx]);
                seq_equality_lemma(main@, sub@, i as int);
            }
            return true;
        }
        
        i += 1;
    }
    
    proof {
        assert(forall|k: int| 0 <= k <= max_i ==> !subrange_matches(main@, sub@, k));
    }
    
    false
}
// </vc-code>

}
fn main() {}