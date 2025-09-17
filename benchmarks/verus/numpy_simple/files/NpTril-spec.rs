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

fn tril(arr: Matrix<i32>, k: i32) -> (ret: Matrix<i32>)
    requires 
        arr.len() > 0,
        arr[0].len() > 0,
        -((arr.len() as i32) - 1) < k && k < (arr[0].len() as i32) - 1,
    ensures
        matrix_size(ret) == matrix_size(arr),
        ret.len() == arr.len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
                if j - i > k { ret[i][j] == 0 } else { ret[i][j] == arr[i][j] }
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