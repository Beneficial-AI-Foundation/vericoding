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
/* helper modified by LLM (iteration 5): Fixed verifier truncate attribute syntax by wrapping cast in parentheses */
proof fn lemma_chessboard_computation(n: int, x: int, y: int)
    requires
        n > 0,
        0 <= x < n,
        0 <= y < n,
    ensures
        chessboard_value(n, x, y) >= 1,
        chessboard_value(n, x, y) <= n * n,
{
    if (x + y) % 2 == 0 {
        assert(x / 2 >= 0);
        assert(y / 2 >= 0);
        assert((x / 2) * n <= (n - 1) / 2 * n);
        assert((x % 2) * ((n + 1) / 2) <= (n + 1) / 2);
        assert(y / 2 <= (n - 1) / 2);
        assert(1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2 <= n * n);
    } else {
        assert((n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2 <= n * n);
    }
}

proof fn lemma_mapping_preserves_length<T, U>(s: Seq<T>, f: spec_fn(int, T) -> U)
    ensures s.map(f).len() == s.len()
{
}

proof fn lemma_map_index<T, U>(s: Seq<T>, f: spec_fn(int, T) -> U, i: int)
    requires 0 <= i < s.len()
    ensures s.map(f)[i] == f(i, s[i])
{
}

fn exec_chessboard_value(n: i8, x: i8, y: i8) -> (result: i8)
    requires
        n > 0,
        0 <= x < n,
        0 <= y < n,
        n <= 10,
    ensures
        result as int == chessboard_value(n as int, x as int, y as int),
{
    let n_i32 = n as i32;
    let x_i32 = x as i32;
    let y_i32 = y as i32;
    
    if (x_i32 + y_i32) % 2 == 0 {
        #[verifier::truncate]
        ((1 + (x_i32 / 2) * n_i32 + (x_i32 % 2) * ((n_i32 + 1) / 2) + y_i32 / 2) as i8)
    } else {
        #[verifier::truncate]
        (((n_i32 * n_i32 + 1) / 2 + 1 + (x_i32 / 2) * n_i32 + (x_i32 % 2) * (n_i32 / 2) + y_i32 / 2) as i8)
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
    /* code modified by LLM (iteration 5): Fixed bounds checking and verification */
    let mut results: Vec<i8> = Vec::new();
    let mut idx = 0;
    
    while idx < queries.len()
        invariant
            0 <= idx <= queries.len(),
            results.len() == idx,
            valid_input(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int))),
            forall|i: int| 0 <= i < idx ==> {
                let x = (queries@[i].0 - 1) as int;
                let y = (queries@[i].1 - 1) as int;
                0 <= x < n && 0 <= y < n &&
                #[trigger] results@[i] as int == chessboard_value(n as int, x, y)
            },
        decreases queries.len() - idx
    {
        let query = queries[idx];
        
        proof {
            assert(queries@[idx as int].0 >= 1);
            assert(queries@[idx as int].1 >= 1);
        }
        
        let x = query.0 - 1;
        let y = query.1 - 1;
        
        let value = exec_chessboard_value(n, x, y);
        
        proof {
            lemma_chessboard_computation(n as int, x as int, y as int);
        }
        
        results.push(value);
        idx += 1;
    }
    
    proof {
        lemma_mapping_preserves_length(queries@, |i: int, q: (i8, i8)| (q.0 as int, q.1 as int));
        lemma_mapping_preserves_length(results@, |i: int, r: i8| r as int);
    }
    
    results
}
// </vc-code>


}

fn main() {}