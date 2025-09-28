// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed compilation errors by replacing outdated vstd lemmas */
proof fn lemma_uniqueness_of_majority(s: Seq<i32>, majority_candidate: i32)
    requires
        count_occurrences(majority_candidate, s) > s.len() / 2,
    ensures
        forall|x: i32| x != majority_candidate ==> count_occurrences(x, s) <= s.len() / 2,
{
    let n = s.len();
    assert forall|x: i32| x != majority_candidate implies count_occurrences(x, s) <= s.len() / 2 by {
        let p_maj = |y: i32| y == majority_candidate;
        let p_x = |y: i32| y == x;

        assert forall|y: i32| p_maj(y) implies !p_x(y) by {}; 
        
        vstd::seq_lib::lemma_len_filter_add(s, p_maj, p_x);

        let count_maj = count_occurrences(majority_candidate, s);
        let count_x = count_occurrences(x, s);
        
        assert(count_maj + count_x <= n);
    }
}

fn count_occurrences_exec(x: i32, lst: &Vec<i32>) -> (c: usize)
    ensures
        c == count_occurrences(x, lst@),
{
    let mut c: usize = 0;
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            i <= lst.len(),
            c == count_occurrences(x, lst@.subrange(0, i as int)),
    {
        if lst[i] == x {
            c = c + 1;
        }
        i = i + 1;
    }
    c
}
// </vc-helpers>

// <vc-spec>
fn find_majority_element(lst: &Vec<i32>) -> (result: i32)
    ensures ({
        let lst_seq = lst@;
        let n = lst_seq.len();
        let majority = count_occurrences(result, lst_seq) > n / 2 && 
                      forall|x: i32| count_occurrences(x, lst_seq) <= n / 2 || x == result;
        (result == -1 ==> forall|x: i32| count_occurrences(x, lst_seq) <= n / 2) &&
        (result != -1 ==> majority)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no logical change, fixed compilation errors in helpers */
    let n = lst.len();
    if n == 0 {
        return -1;
    }

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| 0 <= k < (i as int) ==> count_occurrences(lst@[k], lst@) <= n / 2,
    {
        let candidate = lst[i];
        let count = count_occurrences_exec(candidate, lst);
        
        if count > n / 2 {
            proof {
                lemma_uniqueness_of_majority(lst@, candidate);
            }
            return candidate;
        }
        
        i = i + 1;
    }

    proof {
        assert forall|x: i32| count_occurrences(x, lst@) <= n / 2 by {
            if lst@.contains(x) {
                let k = lst@.index_of(x);
                assert(lst@[k] == x);
            } else {
                assert(count_occurrences(x, lst@) == 0);
            }
        }
    }
    
    return -1;
}
// </vc-code>

}
fn main() {}