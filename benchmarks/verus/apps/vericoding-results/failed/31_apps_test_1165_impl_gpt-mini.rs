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
/* helper modified by LLM (iteration 5): lemma extracting bounds from valid_input */
proof fn lemma_query_bounds(n: int, m: int, a: Seq<int>, queries: Seq<(int, int, int)>, idx: int)
    requires
        valid_input(n, m, a, queries),
        0 <= idx < queries.len(),
{
    assert(queries.contains(queries[idx]));
    assert(1 <= queries[idx].0 && queries[idx].0 <= queries[idx].1 && queries[idx].1 <= n);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<(i8, i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)))
    ensures valid_result(a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate queries with proofs of bounds and safe indexing */
    let mut result: Vec<i8> = Vec::new();
    let mut qi: usize = 0;
    let m_us: usize = queries.len();
    let n_us: usize = a.len();

    while qi < m_us
        invariant
            qi <= m_us,
            result.len() == qi,
        decreases m_us - qi
    {
        proof {
            // use lemma to obtain bounds for this query
            lemma_query_bounds(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)), qi as int);
        }

        let (l, r, x) = queries[qi];

        proof {
            let l_i: int = l as int;
            let r_i: int = r as int;
            assert(1 <= l_i);
            assert(l_i <= r_i);
            assert(r_i <= n_us as int);
        }

        let l0: usize = (l as usize) - 1;
        let r0: usize = (r as usize) - 1;

        proof {
            assert(r0 < n_us);
        }

        let mut j: usize = l0;
        let mut found: bool = false;
        let mut pos: usize = 0;

        while j <= r0
            invariant
                l0 <= j,
                j <= r0 + 1,
                r0 < n_us,
                found ==> (l0 <= pos && pos <= r0),
            decreases (r0 + 1) - j
        {
            if a[j] != x {
                pos = j;
                found = true;
                break;
            }
            j += 1;
        }

        if !found {
            result.push(-1);
        } else {
            result.push(((pos + 1) as i8));
        }

        qi += 1;
    }

    result
}

// </vc-code>


}

fn main() {}