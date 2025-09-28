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
    /* code modified by LLM (iteration 4): use constructive approach to avoid unsupported mutation */
    let mut ret = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= (i as int) && (i as int) <= arr.len(),
            ret.len() == i,
            forall|r: int| 0 <= r < (i as int) ==> ret[r].len() == arr[r].len(),
            forall|r: int, c: int|
                0 <= r < (i as int) && 0 <= c < arr[r].len() ==>
                    if c - r > k as int { ret[r][c] == 0 } else { ret[r][c] == arr[r][c] },
            (i as int) > 0 ==> ret[0].len() == arr[0].len(),
        decreases arr.len() - i
    {
        let mut new_row = Vec::new();
        let mut j: usize = 0;
        let row_len = arr[i].len();

        while j < row_len
            invariant
                0 <= (j as int) && (j as int) <= row_len,
                new_row.len() == j,
                forall|c: int| 0 <= c < (j as int) ==>
                    if c - (i as int) > k as int { new_row[c] == 0 } else { new_row[c] == arr[i as int][c] },
            decreases row_len - j
        {
            if (j as isize) - (i as isize) > k as isize {
                new_row.push(0i8);
            } else {
                new_row.push(arr[i][j]);
            }
            j = j + 1;
        }
        ret.push(new_row);
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}