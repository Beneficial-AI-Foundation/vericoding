// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
proof fn candidate_and_count(seq: Seq<i32>) -> (i32, nat)
    ensures
        if result.0 == -1 {
            result.1 == 0
        } else {
            result.1 > 0
        },
        if result.0 != -1 {
            count_occurrences(result.0, seq) > 0
        } else {
            forall|x: i32| count_occurrences(x, seq) == 0
        }
{
    if seq.len() == 0 {
        (-1, 0)
    } else {
        let (candidate_rest, count_rest) = candidate_and_count(seq.subrange(1, seq.len() as int));
        if count_rest == 0 {
            (seq[0], 1)
        } else if candidate_rest == seq[0] {
            (candidate_rest, count_rest + 1)
        } else {
            (candidate_rest, count_rest - 1)
        }
    }
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
    /* code modified by LLM (iteration 5): Fixed result variable name conflict */
    let n = lst.len();
    if n == 0 {
        return -1;
    }
    
    let (candidate, _) = candidate_and_count(lst@);
    
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            count == count_occurrences(candidate, lst@.subrange(0, i as int))
    {
        if lst[i] == candidate {
            count += 1;
        }
        i += 1;
    }
    
    let final_result = if count > n / 2 {
        candidate
    } else {
        -1
    };
    final_result
}
// </vc-code>

}
fn main() {}