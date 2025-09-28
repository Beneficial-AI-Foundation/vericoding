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
/* code modified by LLM (iteration 5): added #[trigger] to forall quantifier in inner invariant to resolve trigger inference error */
{
    let mut result: Vec<i8> = Vec::with_capacity(m as usize);
    proof {
        assert(valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int))));
    }
    let mut i: usize = 0;
    while i < m as usize
        invariant
            0 <= i <= m as int,
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> {
                let l = queries@[k].0 as int;
                let r = queries@[k].1 as int;
                let x = queries@[k].2 as int;
                let res = result@[k] as int;
                if res == -1 {
                    forall|j: int| l <= j <= r ==> a@[j-1] == x
                } else if l <= res <= r {
                    a@[res-1] != x &&
                    forall|j: int| l <= j < res ==> a@[j-1] == x
                } else {
                    false
                }
            },
        decreases (m as int - i)
    {
        let query = queries[i];
        let l = query.0;
        let r = query.1;
        let x = query.2;
        let mut pos = l;
        while pos <= r &&
              a[(pos - 1) as usize] == x
            invariant
                l as int <= pos as int <= r as int + 1,
                #[trigger] forall|j: int| l as int <= j < pos as int ==> #[trigger] a@[(j - 1)] == x as int,
            decreases (r as int - pos as int + 1)
        {
            pos = pos + 1;
        }
        proof {
            if pos <= r {
                assert(forall|j: int| l as int <= j < pos as int ==> a@[(j - 1)] == x as int);
                assert(a@[(pos - 1) as int] != x as int);
            } else {
                assert(forall|j: int| l as int <= j <= r as int ==> a@[(j - 1)] == x as int);
            }
        }
        if pos > r {
            result.push(-1i8);
        } else {
            result.push(pos);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}