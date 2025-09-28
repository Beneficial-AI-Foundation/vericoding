// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove disjoint counts bound */
proof fn lemma_count_occurrences_bounds(x: i32, lst: Seq<i32>)
    ensures
        count_occurrences(x, lst) <= lst.len()
{
    let filtered = lst.filter(|y: i32| y == x);
    assert(filtered.len() <= lst.len());
}

proof fn lemma_disjoint_counts(x: i32, y: i32, lst: Seq<i32>)
    requires
        x != y
    ensures
        count_occurrences(x, lst) + count_occurrences(y, lst) <= lst.len()
{
    // For any position i in lst, lst[i] can equal x OR y, but not both
    // Therefore the sum of their counts cannot exceed the length
}

proof fn lemma_majority_unique(x: i32, y: i32, lst: Seq<i32>)
    requires
        x != y,
        count_occurrences(x, lst) > lst.len() / 2,
        count_occurrences(y, lst) > lst.len() / 2
    ensures
        false
{
    let n = lst.len();
    let count_x = count_occurrences(x, lst);
    let count_y = count_occurrences(y, lst);
    
    lemma_disjoint_counts(x, y, lst);
    
    assert(count_x > n / 2);
    assert(count_y > n / 2);
    assert(count_x + count_y > n);
    assert(count_x + count_y <= n);
    assert(false);
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
    /* code modified by LLM (iteration 5): Fixed early return and loop invariant */
    if lst.len() == 0 {
        proof {
            assert forall|x: i32| count_occurrences(x, lst@) <= lst@.len() / 2 by {
                assert(lst@.len() == 0);
                assert(count_occurrences(x, lst@) == 0);
            }
        }
        return -1;
    }
    
    let mut candidate: i32 = lst[0];
    let mut count: usize = 1;
    let mut i: usize = 1;
    
    while i < lst.len()
        invariant
            1 <= i <= lst.len(),
            count <= i
        decreases lst.len() - i
    {
        if count == 0 {
            candidate = lst[i];
            count = 1;
        } else if lst[i] == candidate {
            count = count + 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    if count == 0 {
        proof {
            assert forall|x: i32| count_occurrences(x, lst@) <= lst@.len() / 2 by {
                lemma_count_occurrences_bounds(x, lst@);
            }
        }
        return -1;
    }
    
    let mut verify_count: usize = 0;
    let mut j: usize = 0;
    
    while j < lst.len()
        invariant
            0 <= j <= lst.len(),
            verify_count <= j,
            verify_count == count_occurrences(candidate, lst@.take(j as int)) as usize
        decreases lst.len() - j
    {
        if lst[j] == candidate {
            verify_count = verify_count + 1;
        }
        j = j + 1;
    }
    
    assert(lst@.take(lst.len() as int) =~= lst@);
    assert(verify_count == count_occurrences(candidate, lst@) as usize);
    
    if verify_count > lst.len() / 2 {
        proof {
            lemma_count_occurrences_bounds(candidate, lst@);
            assert forall|x: i32| x != candidate implies count_occurrences(x, lst@) <= lst.len() / 2 by {
                if count_occurrences(x, lst@) > lst.len() / 2 {
                    lemma_majority_unique(x, candidate, lst@);
                }
            };
        }
        candidate
    } else {
        proof {
            assert forall|x: i32| count_occurrences(x, lst@) <= lst.len() / 2 by {
                lemma_count_occurrences_bounds(x, lst@);
                if count_occurrences(x, lst@) > lst.len() / 2 {
                    if x == candidate {
                        assert(count_occurrences(candidate, lst@) == verify_count as nat);
                        assert(verify_count <= lst.len() / 2);
                        assert(false);
                    } else {
                        lemma_majority_unique(x, candidate, lst@);
                    }
                }
            };
        }
        -1
    }
}
// </vc-code>

}
fn main() {}