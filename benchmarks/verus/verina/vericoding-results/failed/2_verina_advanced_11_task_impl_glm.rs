// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
proof fn count_occurrences_ge_zero(x: i32, lst: Seq<i32>) {
    assert(count_occurrences(x, lst) >= 0);
}

proof fn count_occurrences_le_len(x: i32, lst: Seq<i32>) {
    assert(count_occurrences(x, lst) <= lst.len());
}

proof fn count_occurrences_subset(x: i32, lst: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= lst.len(),
    ensures
        count_occurrences(x, lst.subrange(i, j)) <= count_occurrences(x, lst),
{
}

proof fn count_occurrences_remove(x: i32, lst: Seq<i32>, i: int)
    requires
        0 <= i < lst.len(),
    ensures
        count_occurrences(x, lst.remove(i)) <= count_occurrences(x, lst),
        lst[i] != x ==> count_occurrences(x, lst.remove(i)) == count_occurrences(x, lst),
        lst[i] == x ==> count_occurrences(x, lst.remove(i)) == count_occurrences(x, lst) - 1,
{
}

spec fn has_majority(lst: Seq<i32>) -> bool {
    exists|x: i32| count_occurrences(x, lst) > lst.len() / 2
}

/* helper modified by LLM (iteration 2): fixed return type from int to i32 */
spec fn majority_candidate(lst: Seq<i32>) -> i32 {
    if lst.len() == 0 {
        -1 as i32
    } else if count_occurrences(lst[0], lst) > lst.len() / 2 {
        lst[0]
    } else {
        majority_candidate(lst.subrange(1, lst.len() as int))
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
    /* code modified by LLM (iteration 5): fixed compilation error in filter pattern */
    if lst.is_empty() {
        return -1 as i32;
    }
    
    let mut candidate = lst[0];
    let mut count = 1usize;
    let n = lst.len();
    
    let mut i = 1usize;
    while i < n
        invariant
            0 < (i as int) <= (n as int),
            (count as int) > 0,
            forall|k: int| 0 <= k < (i as int) ==> (count_occurrences(candidate, lst@.subrange(0, i as int)) > count_occurrences(k as i32, lst@.subrange(0, i as int)) || k as i32 == candidate),
            count_occurrences(candidate, lst@.subrange(0, i as int)) >= (count as int),
            (count as int) <= (i as int),
        decreases (n as int) - (i as int)
    {
        if lst[i] == candidate {
            count += 1;
        } else {
            if count == 1 {
                candidate = lst[i];
            } else {
                count -= 1;
            }
        }
        i += 1;
    }
    
    let final_count = lst.iter().filter(|x| *x == candidate).count();
    
    if final_count > n / 2 {
        candidate
    } else {
        -1 as i32
    }
}
// </vc-code>

}
fn main() {}