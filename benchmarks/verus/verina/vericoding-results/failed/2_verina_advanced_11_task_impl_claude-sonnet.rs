// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): improved lemma_majority_unique and added inductive lemmas */
proof fn lemma_majority_unique(lst: Seq<i32>, x: i32, y: i32)
    requires
        count_occurrences(x, lst) > lst.len() / 2,
        count_occurrences(y, lst) > lst.len() / 2
    ensures x == y
{
    if x != y {
        assert(count_occurrences(x, lst) + count_occurrences(y, lst) > lst.len());
        lemma_disjoint_counts(lst, x, y);
        assert(false);
    }
}

proof fn lemma_disjoint_counts(lst: Seq<i32>, x: i32, y: i32)
    requires x != y
    ensures count_occurrences(x, lst) + count_occurrences(y, lst) <= lst.len()
{
    lemma_count_sum_bound(lst, x, y, 0);
}

proof fn lemma_count_sum_bound(lst: Seq<i32>, x: i32, y: i32, k: int)
    requires x != y, 0 <= k <= lst.len()
    ensures count_occurrences(x, lst.subrange(0, k)) + count_occurrences(y, lst.subrange(0, k)) <= k
    decreases k
{
    if k == 0 {
        assert(lst.subrange(0, 0) =~= Seq::<i32>::empty());
    } else {
        lemma_count_sum_bound(lst, x, y, k - 1);
        let prev = lst.subrange(0, k - 1);
        let curr = lst.subrange(0, k);
        assert(curr =~= prev.push(lst[k - 1]));
    }
}

proof fn lemma_count_bound(lst: Seq<i32>, x: i32)
    ensures count_occurrences(x, lst) <= lst.len()
{
}

proof fn lemma_filter_properties(lst: Seq<i32>, x: i32, i: int)
    requires 0 <= i < lst.len()
    ensures
        lst[i] == x ==> count_occurrences(x, lst.subrange(0, i+1)) == count_occurrences(x, lst.subrange(0, i)) + 1,
        lst[i] != x ==> count_occurrences(x, lst.subrange(0, i+1)) == count_occurrences(x, lst.subrange(0, i))
{
    let prev = lst.subrange(0, i);
    let curr = lst.subrange(0, i + 1);
    assert(curr =~= prev.push(lst[i]));
}

proof fn lemma_subrange_equivalence(lst: Seq<i32>, len: int)
    requires len == lst.len()
    ensures lst.subrange(0, len) =~= lst
{
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
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and loop invariants */
    if lst.len() == 0 {
        return -1;
    }
    
    let mut candidate = lst[0];
    let mut count = 1i32;
    let mut i = 1usize;
    
    while i < lst.len()
        invariant
            1 <= i <= lst.len(),
            count >= 0
        decreases lst.len() - i
    {
        if lst[i] == candidate {
            if count < i32::MAX {
                count = count + 1;
            }
        } else {
            count = count - 1;
            if count == 0 && i + 1 < lst.len() {
                candidate = lst[i + 1];
                count = 1;
                i = i + 1;
            }
        }
        i = i + 1;
    }
    
    let mut verify_count = 0usize;
    let mut j = 0usize;
    
    while j < lst.len()
        invariant
            0 <= j <= lst.len(),
            verify_count == count_occurrences(candidate, lst@.subrange(0, j as int))
        decreases lst.len() - j
    {
        if lst[j] == candidate {
            verify_count = verify_count + 1;
        }
        proof {
            lemma_filter_properties(lst@, candidate, j as int);
        }
        j = j + 1;
    }
    
    proof {
        lemma_subrange_equivalence(lst@, lst.len() as int);
        assert(lst@.subrange(0, lst.len() as int) =~= lst@);
        assert(verify_count == count_occurrences(candidate, lst@));
    }
    
    if verify_count > lst.len() / 2 {
        proof {
            assert(count_occurrences(candidate, lst@) > lst@.len() / 2);
            assert(forall|y: i32| y != candidate ==> count_occurrences(y, lst@) <= lst@.len() / 2) by {
                if exists|y: i32| y != candidate && count_occurrences(y, lst@) > lst@.len() / 2 {
                    let y = choose|y: i32| y != candidate && count_occurrences(y, lst@) > lst@.len() / 2;
                    lemma_majority_unique(lst@, candidate, y);
                    assert(false);
                }
            }
        }
        candidate
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}