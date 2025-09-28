// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: Seq<int>) -> bool {
    a.len() > 0
}

spec fn is_sorted(x: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < x.len() ==> x[i] <= x[j]
}

spec fn thanos_sort(x: Seq<int>) -> int
    recommends x.len() > 0
    decreases x.len()
{
    let len = x.len() as int;
    if is_sorted(x) {
        len
    } else {
        let first_half = x.subrange(0, len / 2);
        let second_half = x.subrange(len / 2, len);
        let left_result = thanos_sort(first_half);
        let right_result = thanos_sort(second_half);
        if left_result > right_result { left_result } else { right_result }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed slice method to use subrange and to_vec */
proof fn lemma_thanos_sort_bounds(x: Seq<int>)
    requires x.len() > 0
    ensures 1 <= thanos_sort(x) <= x.len()
    decreases x.len()
{
    let len = x.len() as int;
    if is_sorted(x) {
        // Base case: sorted sequence returns its length
    } else {
        let first_half = x.subrange(0, len / 2);
        let second_half = x.subrange(len / 2, len);
        if first_half.len() > 0 {
            lemma_thanos_sort_bounds(first_half);
        }
        if second_half.len() > 0 {
            lemma_thanos_sort_bounds(second_half);
        }
    }
}

fn is_sorted_check(a: &Vec<i8>) -> (result: bool)
    ensures result == is_sorted(a@.map(|i, x| x as int))
{
    if a.len() <= 1 {
        return true;
    }
    
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall|k: int, j: int| 0 <= k < j < i + 1 ==> a@[k] as int <= a@[j] as int,
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}

fn exec_thanos_sort(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0
    ensures result as int == thanos_sort(a@.map(|i, x| x as int))
    decreases a.len()
{
    if is_sorted_check(&a) {
        a.len()
    } else {
        let mid = a.len() / 2;
        let first_half = a@.subrange(0, mid as int).to_vec();
        let second_half = a@.subrange(mid as int, a.len() as int).to_vec();
        
        let left_result = if first_half.len() > 0 {
            exec_thanos_sort(first_half)
        } else {
            0
        };
        
        let right_result = if second_half.len() > 0 {
            exec_thanos_sort(second_half)
        } else {
            0
        };
        
        if left_result > right_result {
            left_result
        } else {
            right_result
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: usize)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        result as int == thanos_sort(a@.map(|i, x| x as int)),
        1 <= result <= a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use exec helper function */
    proof {
        let ghost mapped_seq: Seq<int> = a@.map(|i, x| x as int);
        lemma_thanos_sort_bounds(mapped_seq);
    }
    
    exec_thanos_sort(a)
}
// </vc-code>


}

fn main() {}