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
/* helper modified by LLM (iteration 5): changed to use int indices and sequence indexing to avoid bounds issues */
fn find_first_not_equal_vec(a: &Vec<i8>, l: usize, r: usize, x: i8) -> (result: i8)
    requires l <= r && r < a.len()
    ensures
        result == -1 ==> forall|i: int| (l as int) <= i <= (r as int) ==> 0 <= i < a@.len() && a@[i] == x,
        result != -1 ==> { 
            let idx = result as int;
            (l as int) <= idx <= (r as int) && 0 <= idx < a@.len() && a@[idx] != x && forall|i: int| (l as int) <= i < idx ==> 0 <= i < a@.len() && a@[i] == x
        }
{
    let a_seq = a@;
    let mut i = l as int;
    while i <= (r as int)
        invariant
            (l as int) <= i <= (r as int) + 1,
            forall|j: int| (l as int) <= j < i ==> 0 <= j < a_seq.len() && a_seq[j] == x,
        decreases ((r as int) - i)
    {
        if a_seq[i] != x {
            return #[verifier::truncate] i as i8;
        }
        i += 1;
    }
    -1
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<(i8, i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)))
    ensures valid_result(a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed underflow with truncate casts and updated helper call */
{
    let mut result = Vec::with_capacity(m as usize);
    for q in queries {
        let (l, r, x) = q;
        let l0 = #[verifier::truncate] (l - 1) as usize;
        let r0 = #[verifier::truncate] (r - 1) as usize;
        let idx_0 = find_first_not_equal_vec(&a, l0, r0, x);
        if idx_0 == -1 {
            result.push(-1);
        } else {
            result.push(idx_0 + 1);
        }
    }
    result
}
// </vc-code>


}

fn main() {}