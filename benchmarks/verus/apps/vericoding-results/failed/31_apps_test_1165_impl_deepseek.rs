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
proof fn lemma_array_access(a: Seq<int>, idx: int)
    requires
        idx > 0,
        0 <= idx - 1 < a.len(),
    ensures
        idx > 0,
{
    assert(idx > 0);
}

proof fn lemma_array_access_safe(a: Seq<int>, idx: int)
    requires
        0 <= idx < a.len(),
        idx > 0,
    ensures
        0 <= idx-1 < a.len(),
{}

spec fn has_match_in_range(a: Seq<int>, l: int, r: int, x: int) -> bool {
    exists|j: int| l <= j <= r && 0 <= j-1 < a.len() && a[j-1] == x
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<(i8, i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)))
    ensures valid_result(a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat/int type usage errors */
    let mut result = Vec::new();
    
    let queries = queries;
    let a = a;
    
    for q in 0..m as usize {
        let tuple = queries[q];
        let ql = tuple.0;
        let qr = tuple.1;
        let qx = tuple.2;
        let l = ql as i32;
        let r = qr as i32;
        let x = qx as i32;
        
        let mut found = -1i8;
        
        for j in l..=r {
            if j > 0 {
                let idx_val = (j - 1) as usize;
                if idx_val < a.len() && a[idx_val] != qx {
                    found = j as i8;
                    break;
                }
            }
        }
        
        result.push(found);
    }
    
    result
}
// </vc-code>


}

fn main() {}