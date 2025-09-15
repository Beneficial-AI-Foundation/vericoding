// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): replaced += with explicit addition to prevent overflow */
fn count_occurrences_executable(x: i32, lst: &Vec<i32>) -> nat {
    let mut count: nat = 0;
    let len = lst.len();
    for i in 0..len {
        if lst[i] == x {
            count = count + 1;
        }
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
/* code modified by LLM (iteration 4): added explicit bounds assertion */
{
    let n = lst.len();
    if n == 0 {
        return -1;
    }
    
    // Check each element to see if it's a majority
    for i in 0..n {
        assert(i < n);
        let candidate = lst[i];
        let count = count_occurrences_executable(candidate, lst);
        if count > n / 2 {
            return candidate;
        }
    }
    
    -1
}
// </vc-code>

}
fn main() {}