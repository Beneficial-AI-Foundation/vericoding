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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<(i8, i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)))
    ensures valid_result(a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause to both loops */
    let mut result = Vec::new();
    let mut i = 0;
    while i < m
        invariant
            0 <= i <= m,
            result.len() == i as nat,
            valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int))),
            forall|j: int| 0 <= j < i ==> {
                let l = queries@[j as int].0 as int;
                let r = queries@[j as int].1 as int;
                let x = queries@[j as int].2 as int;
                (result@[j as int] as int == -1 ==> (forall|k: int| l <= k <= r ==> 0 <= k-1 < a@.len() && #[trigger] a@[k-1] as int == x)) &&
                (result@[j as int] as int != -1 ==> l <= result@[j as int] as int <= r && 0 <= result@[j as int] as int - 1 < a@.len() && #[trigger] a@[result@[j as int] as int - 1] as int != x)
            },
        decreases m - i
    {
        let query = queries[i as usize];
        let l = query.0;
        let r = query.1;
        let x = query.2;
        
        let mut found = -1i8;
        let mut j = l;
        while j <= r
            invariant
                l <= j <= r + 1,
                (found == -1 ==> (forall|k: int| l as int <= k < j as int ==> 0 <= k-1 < a@.len() && #[trigger] a@[k-1] as int == x as int)),
                (found != -1 ==> l as int <= found as int <= r as int && 0 <= found as int - 1 < a@.len() && #[trigger] a@[found as int - 1] as int != x as int),
            decreases r - j + 1
        {
            if a[(j - 1) as usize] != x {
                found = j;
                j = r + 1;
            } else {
                j = j + 1;
            }
        }
        result.push(found);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}