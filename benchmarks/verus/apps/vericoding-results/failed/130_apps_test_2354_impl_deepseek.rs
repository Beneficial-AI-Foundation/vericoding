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

proof fn lemma_chessboard_properties(n: nat, x: nat, y: nat)
    requires
        0 <= x < n,
        0 <= y < n,
    ensures
        chessboard_value(n, x, y) >= 1,
        chessboard_value(n, x, y) <= (n * n + 1) as int / 2 + (n * n) as int / 2,
    decreases n,
{
    // Helper lemma for chessboard value bounds
    if (x + y) % 2 == 0 {
        assert(1 <= chessboard_value(n, x, y));
        assert(chessboard_value(n, x, y) <= n * n / 2 + 1);
    } else {
        assert((n * n + 1) / 2 + 1 <= chessboard_value(n, x, y));
        assert(chessboard_value(n, x, y) <= (n * n + 1) / 2 + n * n / 2);
    }
}

spec fn adjust_coordinates(x: int, y: int) -> (int, int)
    ensures
        result.0 == x - 1,
        result.1 == y - 1,
{
    (x - 1, y - 1)
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, queries: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int)))
    ensures valid_result(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int)), results@.map(|i: int, r: i8| r as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error by removing ghost variable declarations */
    let mut results = Vec::new();
    let n_int = n as int;
    
    proof {
        lemma_chessboard_properties(n_int, 0, 0);
    }
    
    let mut i = 0;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let (x_orig, y_orig) = queries@[j];
                let x = x_orig as int - 1;
                let y = y_orig as int - 1;
                0 <= x < n_int && 0 <= y < n_int &&
                results@[j] as int == chessboard_value(n_int, x, y)
            },
        decreases queries.len() - i,
    {
        let query = queries.index(i);
        let (x_orig, y_orig) = *query;
        let x_val = x_orig as int - 1;
        let y_val = y_orig as int - 1;
        
        proof {
            assert(0 <= x_val < n_int && 0 <= y_val < n_int);
        }
        
        let value = if (x_val + y_val) % 2 == 0 {
            1 + (x_val / 2) * n_int + (x_val % 2) * ((n_int + 1) / 2) + y_val / 2
        } else {
            (n_int * n_int + 1) / 2 + 1 + (x_val / 2) * n_int + (x_val % 2) * (n_int / 2) + y_val / 2
        };
        
        results.push((value as i8));
        proof {
            assert(results@[i] as int == value);
            assert(value == chessboard_value(n_int, x_val, y_val));
        }
        
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}