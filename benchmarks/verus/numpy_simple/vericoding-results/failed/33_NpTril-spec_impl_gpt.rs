// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): complete lemma to relate usize and int ordering */
proof fn lemma_usize_lt_to_int(i: usize, n: usize)
    requires
        i < n,
    ensures
        (i as int) < (n as int),
{
    assert((i as int) < (n as int));
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
    /* code modified by LLM (iteration 5): guard arr indexing to satisfy preconditions; keep invariants to establish postcondition */
    let rows = arr.len();
    let cols = arr[0].len();
    let mut ret: Matrix<i8> = Vec::new();

    let mut i: usize = 0;
    while i < rows
        invariant
            ret.len() == i,
            0 <= i <= rows,
            rows == arr.len(),
            cols == arr[0].len(),
            rows > 0,
            cols > 0,
            forall|ii: int| 0 <= ii < i ==> (ret@[ii]).len() == cols,
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < cols ==>
                    if jj - ii > k as int { (ret@[ii])@[jj] == 0 } else { (ret@[ii])@[jj] == (arr@[ii])@[jj] },
        decreases (rows as int) - (i as int)
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                row.len() == j,
                0 <= j <= cols,
                0 <= i < rows,
                rows == arr.len(),
                cols == arr[0].len(),
                forall|jj: int|
                    0 <= jj < j ==>
                        if jj - (i as int) > k as int { row@[jj] == 0 } else { row@[jj] == (arr@[i as int])@[jj] },
            decreases (cols as int) - (j as int)
        {
            proof { assert((i as int) < (arr.len() as int)); }
            let cond: bool = ((j as int) - (i as int)) > (k as int);
            if cond {
                row.push(0);
            } else {
                if j < arr[i].len() {
                    row.push(arr[i][j]);
                } else {
                    // Out of bounds for this row; push 0 to satisfy safety
                    row.push(0);
                }
            }
            proof {
                let jj: int = j as int;
                if cond {
                    assert(jj - (i as int) > k as int);
                    assert(row@[jj] == 0);
                } else {
                    if j < arr[i].len() {
                        assert(jj < (arr@[i as int]).len());
                        assert(row@[jj] == (arr@[i as int])@[jj]);
                    }
                }
            }
            j = j + 1;
        }
        proof { assert(row.len() == cols); }
        ret.push(row);
        i = i + 1;
    }
    ret
}

// </vc-code>


}
fn main() {}