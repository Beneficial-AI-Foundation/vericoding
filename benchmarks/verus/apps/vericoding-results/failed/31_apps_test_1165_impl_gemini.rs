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
/* helper modified by LLM (iteration 3): improved triggers */
fn find_first_unequal(a: &Vec<i8>, l: i8, r: i8, x: i8) -> (res: i8)
    requires
        1 <= l,
        l <= r,
        r as int <= a@.len(),
    ensures
        (res == -1 ==> (forall|k: int| l as int <= k <= r as int ==> 
            0 <= k - 1 < a@.len() && (#[trigger] a@[k-1]) as int == (x as int))),
        (res != -1 ==> (l as int <= res as int <= r as int &&
            0 <= (res as int) - 1 < a@.len() && (#[trigger] a@[(res as int) - 1]) as int != (x as int))),
{
    let mut i = l as i32;
    let r_i32 = r as i32;
    while i <= r_i32
        invariant
            l as int <= i as int,
            i as int <= r as int + 1,
            1 <= l <= r,
            r as int <= a@.len(),
            forall|k: int| l as int <= k < i as int ==> 0 <= k - 1 < a@.len() && (#[trigger]a@[k-1]) as int == x as int,
        decreases r_i32 - i
    {
        if a[(i - 1) as usize] != x {
            return i as i8;
        }
        i = i + 1;
    }
    return -1;
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<(i8, i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)))
    ensures valid_result(a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation error (`ghost let` -> `let ghost`) */
    let mut result: Vec<i8> = Vec::new();
    let mut i: i8 = 0;

    let ghost spec_a = a@.map(|_k: int, x: i8| x as int);
    let ghost spec_queries = queries@.map(|_k: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int));

    while i < m
        invariant
            0 <= i <= m,
            spec_a == a@.map(|_k: int, x: i8| x as int),
            spec_queries == queries@.map(|_k: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)),
            valid_input(n as int, m as int, spec_a, spec_queries),
            result.len() == i as nat,
            valid_result(spec_a, spec_queries.take(i as int), result@.map(|_k: int, x: i8| x as int)),
        decreases m - i
    {
        let query = queries[i as usize];
        let l = query.0;
        let r = query.1;
        let x = query.2;
        
        let query_result = find_first_unequal(&a, l, r, x);
        
        result.push(query_result);
        
        i = i + 1;
    }
    
    return result;
}
// </vc-code>


}

fn main() {}