// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn sequence_score(a: Seq<i32>, b: Seq<i32>) -> int {
    a.fold_left(0, |acc: int, x: i32| 
        acc + b.fold_left(0, |acc2: int, y: i32| 
            acc2 + (x as int) * (y as int)))
}

spec fn mod_value() -> int { 998244353 }

spec fn count_type3_queries(queries: Seq<Vec<i32>>) -> int {
    queries.fold_left(0, |acc: int, q: Vec<i32>| 
        if q.len() > 0 && q[0] == 3 { acc + 1 } else { acc })
}

fn process_array_queries(n: usize, m: usize, a: Vec<i32>, b: Vec<i32>, queries: Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires 
        n > 0 && m > 0,
        a.len() == n,
        b.len() == m,
        forall|i: int| 0 <= i < queries.len() ==> queries[i].len() > 0,
    ensures
        result.len() == count_type3_queries(queries@),
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] && #[trigger] result[i] < mod_value(),
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
fn main() {}