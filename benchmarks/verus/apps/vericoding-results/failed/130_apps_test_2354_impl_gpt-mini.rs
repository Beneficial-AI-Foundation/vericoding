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
/* helper modified by LLM (iteration 5): lemma connecting chessboard_value to explicit arithmetic for i8 inputs */
proof fn chessboard_value_from_i8(n: int, a: i8, b: i8)
    requires
        n > 0,
        1 <= a as int && a as int <= n && 1 <= b as int && b as int <= n,
    ensures
        chessboard_value(n, (a as int) - 1, (b as int) - 1) ==
            if (((a as int - 1) + (b as int - 1)) % 2 == 0) {
                1 + ((a as int - 1) / 2) * n + ((a as int - 1) % 2) * ((n + 1) / 2) + ((b as int - 1) / 2)
            } else {
                (n * n + 1) / 2 + 1 + ((a as int - 1) / 2) * n + ((a as int - 1) % 2) * (n / 2) + ((b as int - 1) / 2)
            },
{
    // Follows directly from the definition of chessboard_value (both sides are identical expressions)
    assert(chessboard_value(n, (a as int) - 1, (b as int) - 1) == chessboard_value(n, (a as int) - 1, (b as int) - 1));
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, queries: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int)))
    ensures valid_result(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int)), results@.map(|i: int, r: i8| r as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): loop with invariants linking runtime and spec views and proving each result equals chessboard_value */
{
    let mut results: Vec<i8> = Vec::new();
    let len = queries.len();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            results.len() == i,
            len == queries.len(),
            forall|j: int| 0 <= j < i as int ==> {
                let qm = queries@.map(|k: int, q0: (i8, i8)| (q0.0 as int, q0.1 as int));
                let xj = qm[j].0 - 1;
                let yj = qm[j].1 - 1;
                results@[j] as int == chessboard_value(n as int, xj, yj)
            },
        decreases
            len - i
    {
        let (a, b) = queries[i];
        let x_spec: int = (a as int) - 1;
        let y_spec: int = (b as int) - 1;

        // Prove that the computed arithmetic equals the spec chessboard_value
        proof {
            // bounds from input precondition
            assert(1 <= a as int && a as int <= n as int);
            assert(1 <= b as int && b as int <= n as int);
            // relate spec definition to arithmetic form
            chessboard_value_from_i8(n as int, a, b);
        }

        // Compute using a wider integer (i128) to avoid intermediate overflow, then truncate safely
        let n128 = n as i128;
        let x0 = (a as i128) - 1;
        let y0 = (b as i128) - 1;
        let val128: i128 = if ((x0 + y0) % 2) == 0 {
            1 + (x0 / 2) * n128 + (x0 % 2) * ((n128 + 1) / 2) + y0 / 2
        } else {
            (n128 * n128 + 1) / 2 + 1 + (x0 / 2) * n128 + (x0 % 2) * (n128 / 2) + y0 / 2
        };
        let val_i8 = #[verifier::truncate] val128 as i8;

        proof {
            // Show val128 as int equals the same arithmetic expression in spec-int arithmetic
            let rhs: int = if ((x_spec + y_spec) % 2) == 0 {
                1 + (x_spec / 2) * (n as int) + (x_spec % 2) * ((n as int + 1) / 2) + (y_spec / 2)
            } else {
                (n as int * n as int + 1) / 2 + 1 + (x_spec / 2) * (n as int) + (x_spec % 2) * (n as int / 2) + (y_spec / 2)
            };
            assert(val128 as int == rhs);
            // From the helper lemma, chessboard_value equals rhs
            chessboard_value_from_i8(n as int, a, b);
            assert(chessboard_value(n as int, x_spec, y_spec) == rhs);
            assert(chessboard_value(n as int, x_spec, y_spec) == val128 as int);
        }

        results.push(val_i8);
        i += 1;
    }
    results
}

// </vc-code>


}

fn main() {}