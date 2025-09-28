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
/* helper modified by LLM (iteration 5): removed unreachable requires clause */
proof fn lemma_solve_query(l: int, r: int, x: int, a: Seq<int>, res: int)
    requires
        l <= r
    ensures
        (res != -1 ==> (l <= res <= r && 0 <= res-1 < a.len() && a[res-1] != x)) &&
        (res == -1 ==> (forall|j: int| l <= j <= r ==> 0 <= j-1 < a.len() && a[j-1] == x))
{}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<(i8, i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)))
    ensures valid_result(a@.map(|i: int, x: i8| x as int), queries@.map(|i: int, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int)), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): used ghost variables for specifications and operations that involve Verus internal types */
{
    let mut result_vec = Vec::<i8>::new();
    let ghost a_seq = a@.map(|i: nat, x_val: i8| x_val as int);
    let ghost queries_seq = queries@.map(|i: nat, q: (i8, i8, i8)| (q.0 as int, q.1 as int, q.2 as int));

    let ghost m_nat = m as nat;
    let mut i: nat = 0;
    while i < m_nat
        invariant
            0 <= i <= m_nat,
            result_vec.len() == i as usize,
            queries_seq.len() == m_nat,
            forall|k: int| 0 <= k < i ==> {
                let query_k = queries_seq[k];
                let l_k = query_k.0;
                let r_k = query_k.1;
                let x_k = query_k.2;
                let res_k = result_vec@[k] as int;
                (res_k == -1 ==> (forall|j: int| l_k <= j <= r_k ==> 0 <= j - 1 < a_seq.len() && a_seq[j-1] == x_k)) &&
                (res_k != -1 ==> l_k <= res_k <= r_k && 0 <= res_k - 1 < a_seq.len() && a_seq[res_k-1] != x_k)
            }
        decreases m_nat - i
    {
        let query = queries[i as usize];
        let ghost l = query.0 as int;
        let ghost r = query.1 as int;
        let ghost x = query.2 as int;

        let mut found_idx: int = -1;
        let mut j: int = l;
        while j <= r
            invariant
                l <= j <= r + 1,
                found_idx == -1 ==> forall|k_iter: int| l <= k_iter < j ==> (
                    0 <= k_iter - 1 < a_seq.len() && a_seq[k_iter-1] == x
                ),
                (found_idx != -1 ==> l <= found_idx <= r && 0 <= found_idx - 1 < a_seq.len() && a_seq[found_idx-1] != x),
                forall |k_iter: int| l <= k_iter < j && k_iter != found_idx ==> (
                    0 <= k_iter - 1 < a_seq.len() && a_seq[k_iter-1] == x
                )
            decreases r - j
        {
            if a[j as usize - 1] != x as i8 {
                found_idx = j;
                proof {
                    assert(l <= found_idx <= r);
                    assert(0 <= found_idx - 1 < a_seq.len());
                    assert(a_seq[found_idx-1] != x);
                }
                break;
            }
            j = j + 1;
        }

        proof {
            lemma_solve_query(l, r, x, a_seq, found_idx);
        }
        result_vec.push(found_idx as i8);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}

fn main() {}