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
/* helper modified by LLM (iteration 3): Added decreases clause to while loop in is_sorted_exec */
fn is_sorted_exec(a: &Vec<i8>) -> (result: bool)
    ensures
        result == is_sorted(a@.map(|i, x| x as int)),
{
    if a.len() == 0 {
        return true;
    }
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall|j: int, k: int| 0 <= j < k <= i ==> a@[j] <= a@[k],
        decreases a.len() - 1 - i
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

fn thanos_sort_exec(a: &Vec<i8>) -> (result: usize)
    requires
        a.len() > 0,
    ensures
        result as int == thanos_sort(a@.map(|i, x| x as int)),
        1 <= result <= a.len(),
    decreases a.len(),
{
    if is_sorted_exec(a) {
        return a.len();
    }
    
    let len = a.len();
    let mid = len / 2;
    
    let mut first_half: Vec<i8> = Vec::new();
    let mut second_half: Vec<i8> = Vec::new();
    
    let mut i = 0;
    while i < mid
        invariant
            0 <= i <= mid,
            first_half@.len() == i,
            forall|j: int| 0 <= j < i ==> first_half@[j] == a@[j],
        decreases mid - i
    {
        first_half.push(a[i]);
        i = i + 1;
    }
    
    let mut i = mid;
    while i < len
        invariant
            mid <= i <= len,
            second_half@.len() == i - mid,
            forall|j: int| 0 <= j < i - mid ==> second_half@[j] == a@[mid + j],
        decreases len - i
    {
        second_half.push(a[i]);
        i = i + 1;
    }
    
    proof {
        assert(first_half@.map(|i, x| x as int) == a@.map(|i, x| x as int).subrange(0, mid as int));
        assert(second_half@.map(|i, x| x as int) == a@.map(|i, x| x as int).subrange(mid as int, len as int));
    }
    
    let left_result = thanos_sort_exec(&first_half);
    let right_result = thanos_sort_exec(&second_half);
    
    if left_result > right_result {
        left_result
    } else {
        right_result
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
/* code modified by LLM (iteration 3): No change needed, just call the helper function */
{
    thanos_sort_exec(&a)
}
// </vc-code>


}

fn main() {}