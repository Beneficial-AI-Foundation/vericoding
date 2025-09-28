// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): make_vec_i8 constructs Vec<i8> filled with val */
fn make_vec_i8(len: usize, val: i8) -> (result: Vec<i8>)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len as int ==> result[i as usize] == val,
{
    let mut v: Vec<i8> = Vec::new();
    while v.len() < len
        invariant
            v.len() <= len,
            forall|i: int| 0 <= i && i < v.len() as int ==> v[i as usize] == val,
        decreases (len - v.len())
    {
        v.push(val);
    }
    v
}

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
    /* code modified by LLM (iteration 5): avoid Verus 'int' in runtime by using i64 casts for index comparisons */
    let rows = arr.len();
    let cols = arr[0].len();
    let mut ret: Matrix<i8> = Vec::new();

    while ret.len() < rows
        invariant
            ret.len() <= rows,
            forall|i: int, j: int|
                0 <= i && i < ret.len() as int && 0 <= j && j < cols as int ==> 
                    if j - i > k as int { ret[i][j] == 0 } else { ret[i][j] == arr[i][j] },
        decreases rows - ret.len()
    {
        let i_idx = ret.len();
        let mut row: Vec<i8> = Vec::new();
        while row.len() < cols
            invariant
                row.len() <= cols,
                forall|j: int| 0 <= j && j < row.len() as int ==> 
                    if j - (i_idx as int) > k as int { row[j] == 0 } else { row[j] == arr[(i_idx as int)][j] },
            decreases cols - row.len()
        {
            let j_idx = row.len();
            if (j_idx as i64) - (i_idx as i64) > k as i64 {
                row.push(0);
            } else {
                row.push(arr[i_idx][j_idx]);
            }
        }
        ret.push(row);
    }

    ret
}

// </vc-code>


}
fn main() {}