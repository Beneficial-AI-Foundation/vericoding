// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by adding missing braces to spec function */
spec fn is_majority(x: i32, lst: Seq<i32>) -> bool {
    count_occurrences(x, lst) > lst.len() / 2
}

proof fn count_occurrences_def(x: i32, lst: Seq<i32>)
    ensures count_occurrences(x, lst) == lst.filter(|y: i32| y == x).len()
{
}

proof fn majority_uniqueness(lst: Seq<i32>, x: i32, y: i32)
    requires is_majority(x, lst),
    requires is_majority(y, lst),
    ensures x == y
{
    let n = lst.len();
    if x != y {
        assert(count_occurrences(x, lst) > n / 2);
        assert(count_occurrences(y, lst) > n / 2);
        assert(count_occurrences(x, lst) + count_occurrences(y, lst) > n);
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
    /* code modified by LLM (iteration 5): implemented Boyer-Moore majority vote algorithm */
    let lst_seq = lst@;
    let n = lst.len();
    
    if n == 0 {
        return -1;
    }
    
    let mut candidate = lst[0];
    let mut count = 1;
    
    for i in 1..n
        invariant 0 < i <= n,
        invariant count >= 0
    {
        if lst[i] == candidate {
            count = count + 1;
        } else {
            count = count - 1;
            if count == 0 {
                candidate = lst[i];
                count = 1;
            }
        }
    }
    
    let mut actual_count = 0;
    for i in 0..n
        invariant 0 <= i <= n,
        invariant actual_count >= 0
    {
        if lst[i] == candidate {
            actual_count = actual_count + 1;
        }
    }
    
    if actual_count > n / 2 {
        candidate
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}