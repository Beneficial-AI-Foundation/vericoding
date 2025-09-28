// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
type Matrix<T> = Vec<Vec<T>>;

spec fn matrix_size<T>(m: Matrix<T>) -> nat {
    (m.len() * (if m.len() > 0 { m[0].len() } else { 0 })) as nat
}

fn tril(arr: Matrix<i8>, k: i8) -> (ret: Matrix<i8>)
    requires 
        arr.len() > 0,
        arr[0].len() > 0,
        -((arr.len() as i8) - 1) < k && k < (arr[0].len() as i8) - 1,
    ensures
        matrix_size(ret) == matrix_size(arr),
        ret.len() == arr.len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
                if j - i > k as int { ret[i][j] == 0 } else { ret[i][j] == arr[i][j] }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clauses to both loops */
    let mut result: Matrix<i8> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|p: int| 0 <= p < i ==> result[p].len() == arr[0].len(),
            forall|p: int, q: int| 0 <= p < i && 0 <= q < arr[0].len() ==> 
                if q - p > k as int { result[p][q] == 0 } else { result[p][q] == arr[p][q] },
        decreases arr.len() - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < arr[0].len()
            invariant
                j <= arr[0].len(),
                row.len() == j,
                forall|q: int| 0 <= q < j ==> 
                    if q - (i as int) > k as int { row[q] == 0 } else { row[q] == arr[i as int][q] },
            decreases arr[0].len() - j
        {
            if (j as i8) - (i as i8) > k {
                row.push(0);
            } else {
                row.push(arr[i][j]);
            }
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}