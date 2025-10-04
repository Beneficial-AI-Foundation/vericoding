// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn list_maximum(l: Seq<i32>) -> i32 
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else if l.len() == 1 {
        l[0]
    } else {
        let first = l[0];
        let rest_max = list_maximum(l.subrange(1, l.len() as int));
        if first > rest_max { first } else { rest_max }
    }
}

fn solve_max_subarray_query(n: usize, arr: Vec<i32>, queries: Vec<usize>) -> (result: Vec<i32>)
    requires 
        arr.len() > 0,
        arr.len() <= 5,
        queries.len() > 0,
        queries.len() <= 3,
        forall|x: i32| arr@.contains(x) ==> -100 <= x && x <= 100,
        forall|q: usize| queries@.contains(q) ==> 1 <= q && q <= 15,
    ensures
        result.len() == queries.len(),
        forall|x: i32| result@.contains(x) ==> x <= list_maximum(arr@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {
    // let test_result = solve_max_subarray_query(4, vec![3, 1, 2, 4], vec![1, 5]);
    // println!("{:?}", test_result);
    
    // let test_result2 = solve_max_subarray_query(3, vec![1, 2, 3], vec![1, 2, 3]);
    // println!("{:?}", test_result2);
}