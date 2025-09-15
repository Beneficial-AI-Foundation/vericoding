// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
spec fn count_in_range(x: i32, lst: Seq<i32>, start: nat, end: nat) -> nat
    decreases end - start
{
    if start >= end {
        0
    } else if lst[start as int] == x {
        1 + count_in_range(x, lst, start + 1, end)
    } else {
        count_in_range(x, lst, start + 1, end)
    }
}

/* helper modified by LLM (iteration 5): fixed filter equivalence proof with correct sequence operations */
proof fn count_in_range_equiv(x: i32, lst: Seq<i32>)
    ensures count_in_range(x, lst, 0, lst.len() as nat) == count_occurrences(x, lst)
    decreases lst.len()
{
    if lst.len() == 0 {
        assert(lst.filter(|y: i32| y == x).len() == 0);
    } else {
        let lst_rest = lst.subrange(1, lst.len() as int);
        count_in_range_equiv(x, lst_rest);
        
        if lst[0] == x {
            assert(count_in_range(x, lst, 0, lst.len() as nat) == 1 + count_in_range(x, lst_rest, 0, lst_rest.len() as nat));
            assert(lst.filter(|y: i32| y == x).len() == 1 + lst_rest.filter(|y: i32| y == x).len());
        } else {
            assert(count_in_range(x, lst, 0, lst.len() as nat) == count_in_range(x, lst_rest, 0, lst_rest.len() as nat));
            assert(lst.filter(|y: i32| y == x).len() == lst_rest.filter(|y: i32| y == x).len());
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
    /* code modified by LLM (iteration 5): added decreases clause to loops */
    let n = lst.len();
    if n == 0 {
        return -1;
    }
    
    let mut candidate: Option<i32> = None;
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            candidate.is_none() ==> count == 0,
            count <= i,
            candidate.is_some() ==> {
                let c = candidate.unwrap();
                let c_count = count_in_range(c, lst@, 0, i as nat);
                let other_count = i as nat - c_count;
                c_count > other_count + count || (c_count == other_count + count && count == 0)
            }
        decreases n - i
    {
        if count == 0 {
            candidate = Some(lst[i]);
            count = 1;
        } else if candidate.is_some() && candidate.unwrap() == lst[i] {
            count = count + 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    if candidate.is_none() {
        proof {
            assert forall|x: i32| count_occurrences(x, lst@) <= n / 2 by {
                count_in_range_equiv(x, lst@);
            }
        }
        return -1;
    }
    
    let cand = candidate.unwrap();
    let mut final_count: usize = 0;
    let mut j: usize = 0;
    
    while j < n
        invariant 
            0 <= j <= n,
            final_count == count_in_range(cand, lst@, 0, j as nat),
            final_count <= j
        decreases n - j
    {
        if lst[j] == cand {
            final_count = final_count + 1;
        }
        j = j + 1;
    }
    
    proof {
        count_in_range_equiv(cand, lst@);
        assert(final_count == count_in_range(cand, lst@, 0, n as nat));
        assert(count_in_range(cand, lst@, 0, n as nat) == count_occurrences(cand, lst@));
        
        if final_count > n / 2 {
            assert forall|x: i32| count_occurrences(x, lst@) <= n / 2 || x == cand by {
                if x != cand {
                    count_in_range_equiv(x, lst@);
                }
            }
        } else {
            assert forall|x: i32| count_occurrences(x, lst@) <= n / 2 by {
                count_in_range_equiv(x, lst@);
            }
        }
    }
    
    if final_count > n / 2 {
        cand
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}