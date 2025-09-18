// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed named return to match the Verus convention from documentation, while ensuring the type is still returned. */
fn create_initial_row(dim: usize) -> Vec<f64>
{
    let mut row: Vec<f64> = Vec::new();
    let mut j = 0;
    while j < dim {
        row.push(0.0);
        j = j + 1;
    }
    if dim > 0 {
        row.set(0, 1.0);
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: usize) -> (result: Vec<Vec<f64>>)
    requires deg >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `assert()` syntax by removing `by (arith)` which is not a valid prover name. */
{
    let n = x.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    if n > 0 {
        let first_row = create_initial_row(deg + 1);
        result.insert(0, first_row);

        proof {
            assert(result.len() == 1);
        }

        let mut i = 1;
        while i < n
            invariant (
                n == old(n),
                deg == old(deg),
                x == old(x),
                0 < i,
                i <= n,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j].len() == deg + 1,
                forall|j: int| 0 <= j < i ==> result[j][0] == 1.0,
            )
            decreases n - i
        {
            assert(result.len() == i);
            let new_row = create_initial_row(deg + 1);
            result.insert(i, new_row);
            i = i + 1;
        }
    }

    if deg > 0 {
        let mut i = 0;
        while i < n
            invariant (
                n == old(n),
                deg == old(deg),
                x == old(x),
                0 <= i,
                i <= n,
                result.len() == n,
                forall|j: int| 0 <= j < n ==> result[j].len() == deg + 1,
                forall|j: int| 0 <= j < n ==> result[j][0] == 1.0,
                forall|j: int| 0 <= j < i ==> result[j][1] == x[j],
            )
            decreases n - i
        {
            assert(0 <= i && i < n);
            let mut current_row = result.get(i);
            current_row.set(1, x.get(i));
            result.set(i, current_row);
            i = i + 1;
        }
    }

    let mut k = 2;
    while k <= deg
        invariant (
            n == old(n),
            deg == old(deg),
            x == old(x),
            2 <= k,
            k <= deg + 1,
            result.len() == n,
            forall|j: int| 0 <= j < n ==> result[j].len() == deg + 1,
            forall|j: int| 0 <= j < n ==> result[j][0] == 1.0,
            deg > 0 ==> forall|j: int| 0 <= j < n ==> result[j][1] == x[j],
            forall|curr_k: int, j: int| (
                2 <= curr_k && curr_k < k && 0 <= j && j < n
            ) ==> {
                let val_k_minus_1 = result[j][curr_k - 1];
                let val_k_minus_2 = if curr_k >= 2 { result[j][curr_k - 2] } else { 0.0 };
                let x_j = x[j];
                result[j][curr_k] == x_j * val_k_minus_1 - (curr_k - 1) as f64 * val_k_minus_2
            },
        )
        decreases deg - k
    {
        assert(0 <= k && k <= deg);
        let mut i = 0;
        while i < n
            invariant (
                n == old(n),
                deg == old(deg),
                x == old(x),
                k == old(k),
                0 <= i,
                i <= n,
                result.len() == n,
                forall|j: int| 0 <= j < n ==> result[j].len() == deg + 1,
                forall|j: int| 0 <= j < n ==> result[j][0] == 1.0,
                deg > 0 ==> forall|j: int| 0 <= j < n ==> result[j][1] == x[j],
                forall|curr_k: int, j: int| (
                    2 <= curr_k && curr_k < k && 0 <= j && j < n
                ) ==> {
                    let val_k_minus_1 = old(result)[j][curr_k - 1];
                    let val_k_minus_2 = if curr_k >= 2 { old(result)[j][curr_k - 2] } else { 0.0 };
                    let x_j = old(x)[j];
                    old(result)[j][curr_k] == x_j * val_k_minus_1 - (curr_k - 1) as f64 * val_k_minus_2
                },
                // Invariant for result[j][k] for j < i
                forall|j: int| 0 <= j < i ==> {
                    let val_k_minus_1 = result[j][k - 1];
                    let val_k_minus_2 = if k >= 2 { result[j][k - 2] } else { 0.0 };
                    let x_j = x[j];
                    result[j][k] == x_j * val_k_minus_1 - (k - 1) as f64 * val_k_minus_2
                },
            )
            decreases n - i
        {
            assert(0 <= i && i < n);
            let val_k_minus_1 = result.get(i).get(k - 1);
            let val_k_minus_2 = if k >= 2 { result.get(i).get(k - 2) } else { 0.0 };
            let x_i = x.get(i);

            let new_val = x_i * val_k_minus_1 - (k - 1) as f64 * val_k_minus_2;

            let mut current_row = result.get(i);
            current_row.set(k, new_val);
            result.set(i, current_row);

            i = i + 1;
        }
        k = k + 1;
    }

    result
}
// </vc-code>

}
fn main() {}