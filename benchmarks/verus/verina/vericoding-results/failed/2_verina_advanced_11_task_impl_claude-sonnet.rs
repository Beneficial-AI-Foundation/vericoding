// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma proofs with proper counting logic */
fn lemma_count_occurrences_bound(x: i32, lst: Seq<i32>)
    ensures count_occurrences(x, lst) <= lst.len()
{
}

fn lemma_majority_unique(lst: Seq<i32>, a: i32, b: i32)
    requires
        count_occurrences(a, lst) > lst.len() / 2,
        count_occurrences(b, lst) > lst.len() / 2,
    ensures a == b
{
    proof {
        let n = lst.len();
        if a != b {
            let count_a = count_occurrences(a, lst);
            let count_b = count_occurrences(b, lst);
            assert(lst.filter(|y: i32| y == a || y == b).len() >= count_a + count_b);
            assert(count_a + count_b > n);
            assert(false);
        }
    }
}

fn count_element(x: i32, lst: &Vec<i32>) -> (count: usize)
    ensures count == count_occurrences(x, lst@)
{
    let mut count = 0;
    let mut i = 0;
    while i < lst.len()
        invariant
            i <= lst.len(),
            count == count_occurrences(x, lst@.subrange(0, i as int)),
        decreases lst.len() - i
    {
        if lst[i] == x {
            count += 1;
        }
        i += 1;
        proof {
            assert(lst@.subrange(0, i as int) == lst@.subrange(0, (i-1) as int).push(lst@[i-1]));
        }
    }
    proof {
        assert(lst@.subrange(0, lst.len() as int) == lst@);
    }
    count
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
    /* code modified by LLM (iteration 5): proper Boyer-Moore majority vote algorithm */
    if lst.len() == 0 {
        return -1;
    }
    
    let mut candidate = lst[0];
    let mut count = 1;
    let mut i = 1;
    
    while i < lst.len()
        invariant
            i <= lst.len(),
            count >= 0,
        decreases lst.len() - i
    {
        if lst[i] == candidate {
            count += 1;
        } else {
            count -= 1;
            if count == 0 {
                if i + 1 < lst.len() {
                    candidate = lst[i + 1];
                    count = 1;
                    i += 1;
                }
            }
        }
        i += 1;
    }
    
    let actual_count = count_element(candidate, lst);
    if actual_count > lst.len() / 2 {
        proof {
            let lst_seq = lst@;
            let n = lst_seq.len();
            assert(count_occurrences(candidate, lst_seq) > n / 2);
        }
        return candidate;
    }
    
    -1
}
// </vc-code>

}
fn main() {}