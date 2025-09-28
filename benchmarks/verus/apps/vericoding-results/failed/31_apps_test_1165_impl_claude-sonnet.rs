// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: Seq<int>, queries: Seq<(int, int, int)>) -> bool {
    n > 0 && m >= 0 && a.len() == n && queries.len() == m &&
    forall|q| queries.contains(q) ==> 1 <= q.0 <= q.1 <= n
}

spec fn valid_result(a: Seq<int>, queries: Seq<(int, int, int)>, result: Seq<int>) -> bool {
    result.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> {
        let l = queries[i].0;
        let r = queries[i].1;
        let x = queries[i].2;
        (result[i] == -1 ==> (forall|j: int| l <= j <= r ==> 0 <= j-1 < a.len() && #[trigger] a[j-1] == x)) &&
        (result[i] != -1 ==> l <= result[i] <= r && 0 <= result[i]-1 < a.len() && #[trigger] a[result[i]-1] != x)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use int_to_usize function for proper conversion */
fn int_to_usize(i: int) -> (result: usize)
    requires 0 <= i < usize::MAX as int
    ensures result as int == i
{
    i as usize
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<(i8, i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)))
    ensures valid_result(a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int literal and usize conversion */
    let mut result = Vec::new();
    
    for query_idx in 0..queries.len()
        invariant
            result.len() == query_idx,
            valid_result(a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)).subrange(0, query_idx as int), result@.map(|i: int, x: i8| x as int)),
    {
        let query = queries[query_idx];
        let l = query.0;
        let r = query.1;
        let x = query.2;
        
        let mut found_diff = -1i8;
        
        for j in l..(r + 1)
            invariant
                l <= j <= r + 1,
                found_diff == -1 ==> forall|k: int| l <= k < j ==> 0 <= k-1 < a.len() && a@[k-1] == x as int,
                found_diff != -1 ==> l <= found_diff <= r && 0 <= found_diff-1 < a.len() && a@[found_diff-1] != x as int,
        {
            let j_int = j as int;
            let idx = int_to_usize(j_int - 1);
            if a[idx] != x {
                found_diff = j;
                break;
            }
        }
        
        result.push(found_diff);
    }
    
    result
}
// </vc-code>


}

fn main() {}