// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): derive individual bounds from sum bound */
fn lemma_add_bounds(n: usize, a: usize, b: usize)
    requires
        a + b <= n,
    ensures
        a <= n,
        b <= n,
{
    proof {
        assert(a <= a + b);
        assert(a + b <= n);
        assert(a <= n);
        assert(b <= a + b);
        assert(b <= n);
    }
}

// </vc-helpers>

// <vc-spec>
/* Matrix type represented as a 2D vector */
type Matrix<T> = Vec<Vec<T>>;

fn diagonal(arr: Matrix<i8>, k: i8) -> (result: Vec<i8>)
    requires 
        arr.len() > 0,
        arr.len() == arr[0].len(), /* square matrix */
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() == arr.len(),
        -(arr.len() as i8) < k && k < (arr.len() as i8),
    ensures
        if k > 0 {
            result.len() == arr.len() - (k as usize) &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i][i + (k as usize)]
        } else {
            result.len() == arr.len() + ((-k) as usize) &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i + ((-k) as usize)][i]
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): ensure res.len() == i invariant and prove index bounds before push */
{
    let n = arr.len();
    let mut res: Vec<i8> = Vec::new();

    if k > 0 {
        let off = k as usize;
        let mut i: usize = 0;
        while i < n - off
            invariant
                res.len() == i,
                i <= n - off,
                forall|j: int| 0 <= j < (i as int) ==> res@[j] == (arr@[j])@[j + (off as int)],
            decreases (n - off - i),
        {
            proof {
                assert(i < n - off);
                assert(i + off < n);
                assert(i < n);
            }
            res.push(arr[i][i + off]);
            i += 1;
        }
    } else {
        let off = ((-k) as usize);
        let mut i: usize = 0;
        while i < n - off
            invariant
                res.len() == i,
                i <= n - off,
                forall|j: int| 0 <= j < (i as int) ==> res@[j] == (arr@[(j + (off as int))])@[j],
            decreases (n - off - i),
        {
            proof {
                assert(i < n - off);
                assert(i + off < n);
                assert(i < n);
            }
            res.push(arr[i + off][i]);
            i += 1;
        }
    }

    res
}

// </vc-code>


}
fn main() {}