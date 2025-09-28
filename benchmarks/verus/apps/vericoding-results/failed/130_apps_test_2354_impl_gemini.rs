// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, queries: Seq<(int, int)>) -> bool {
    n > 0 && 
    forall|i: int| 0 <= i < queries.len() ==> #[trigger] queries[i].0 >= 1 && #[trigger] queries[i].0 <= n && #[trigger] queries[i].1 >= 1 && #[trigger] queries[i].1 <= n
}

spec fn chessboard_value(n: int, x: int, y: int) -> int {
    if (x + y) % 2 == 0 {
        1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2
    } else {
        (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2
    }
}

spec fn valid_result(n: int, queries: Seq<(int, int)>, results: Seq<int>) -> bool {
    valid_input(n, queries) ==> (
        results.len() == queries.len() &&
        forall|i: int| 0 <= i < queries.len() ==> {
            let x = #[trigger] queries[i].0 - 1;
            let y = #[trigger] queries[i].1 - 1;
            0 <= x < n && 0 <= y < n &&
            #[trigger] results[i] == chessboard_value(n, x, y)
        }
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added a bound on n to prevent overflow. */
fn compute_chessboard_value(n: i64, x: i64, y: i64) -> (result: i64)
    requires
        n > 0,
        n < 1_000_000_000, // prevent i64 overflow
        0 <= x < n,
        0 <= y < n,
    ensures
        result == chessboard_value(n as int, x as int, y as int),
{
    if (x + y) % 2 == 0 {
        1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2
    } else {
        (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, queries: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int)))
    ensures valid_result(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int)), results@.map(|i: int, r: i8| r as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed underflow errors by casting to i64 before subtraction */
    let mut results = Vec::<i8>::new();
    let mut i: usize = 0;
    let ghost n_int = n as int;
    let ghost queries_spec = queries@.map(|_i: int, q: (i8, i8)| (q.0 as int, q.1 as int));

    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            n as int == n_int,
            queries@.map(|_i: int, q: (i8, i8)| (q.0 as int, q.1 as int)) == queries_spec,
            valid_input(n_int, queries_spec),
            forall|j: int| 0 <= j < i ==> #[trigger](results@[j] as int) == chessboard_value(n_int, queries_spec[j].0 - 1, queries_spec[j].1 - 1),
        decreases queries.len() - i
    {
        let query = queries[i];
        let x = query.0 as i64 - 1;
        let y = query.1 as i64 - 1;
        
        let val = compute_chessboard_value(n as i64, x, y);
        let result_i8 = val as i8;
        results.push(result_i8);

        i = i + 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}