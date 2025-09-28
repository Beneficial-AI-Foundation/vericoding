// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_array_uniform(arr: Matrix<i8>)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() == arr[0].len(),
    ensures
        forall|i: int| 0 <= i < arr.len() ==> arr@[i].len() == arr@[0].len(),
{
    // lemma body
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
/* code modified by LLM (iteration 5): fixed compilation error by using isize casts instead of int for executable code */
{
    let n = arr.len();
    let m = arr[0].len();
    let mut ret: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            ret.len() == i,
            0 <= (i as int) <= (n as int),
            forall|ii: int, jj: int| 0 <= ii < (i as int) && 0 <= jj < (m as int) ==> 
                if jj - ii > (k as int) { ret@[ii][jj] == 0 } else { ret@[ii][jj] == arr@[ii][jj] },
        decreases (n - i)
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                row.len() == j,
                0 <= (j as int) <= (m as int),
                forall|jj: int| 0 <= jj < (j as int) ==> 
                    if jj - (i as int) > (k as int) { row@[jj] == 0 } else { row@[jj] == arr@[i as int][jj] },
            decreases (m - j)
        {
            if (j as isize - i as isize) > (k as isize) {
                row.push(0);
            } else {
                row.push(arr[i][j]);
            }
            j = j + 1;
        }
        proof {
            assert(row.len() == m);
        }
        ret.push(row);
        i = i + 1;
    }
    proof {
        assert(ret.len() == n);
        assert(matrix_size(ret) == matrix_size(arr));
        assert forall |i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr@[0].len() ==> 
                (if j - i > k as int { ret@[i][j] == 0 } else { ret@[i][j] == arr@[i][j] })
        by {
            assert(i < ret.len());
        }
    }
    ret
}
// </vc-code>


}
fn main() {}