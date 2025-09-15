// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed count_in_range_lemma parameter types */
proof fn majority_exists_lemma(lst: Seq<i32>, candidate: i32, count: nat)
    requires count_occurrences(candidate, lst) > lst.len() / 2
    ensures count_occurrences(candidate, lst) > lst.len() / 2 && (forall|x: i32| count_occurrences(x, lst) <= lst.len() / 2 || x == candidate)
{
}

proof fn count_in_range_lemma(lst: Seq<i32>, x: i32, start: int, end: int)
    requires 0 <= start <= end <= lst.len()
    ensures count_occurrences(x, lst) == count_occurrences(x, lst.subrange(start, end)) + count_occurrences(x, lst.subrange(0, start)) + count_occurrences(x, lst.subrange(end, lst.len() as int))
{
}

spec fn is_candidate_valid(lst: Seq<i32>, candidate: i32, count: nat) -> bool {
    count_occurrences(candidate, lst) > lst.len() / 2
}

spec fn no_majority_exists(lst: Seq<i32>) -> bool {
    forall|x: i32| count_occurrences(x, lst) <= lst.len() / 2
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
/* code modified by LLM (iteration 5): Fixed vector indexing and return value */
{
    let n = lst.len() as int;
    if n == 0 {
        return -1;
    }
    
    let mut candidate = lst[0];
    let mut count = 1;
    
    let mut i = 1;
    while i < n 
        invariant 0 <= i && i <= n
    {
        if count == 0 {
            candidate = lst[i as usize];
            count = 1;
        } else if lst[i as usize] == candidate {
            count += 1;
        } else {
            count -= 1;
        }
        i += 1;
    }
    
    if count == 0 {
        return -1;
    }
    
    let mut verify_count = 0;
    let mut j = 0;
    while j < n 
        invariant 0 <= j && j <= n
    {
        if lst[j as usize] == candidate {
            verify_count += 1;
        }
        j += 1;
    }
    
    if verify_count > n / 2 {
        candidate
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}