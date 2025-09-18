// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch by using usize for length parameter */
spec fn count_nonzero_up_to(a: Vec<i32>, n: usize) -> usize
    decreases n
{
    if n == 0 {
        0
    } else if n > a.len() {
        count_nonzero_up_to(a, a.len())
    } else {
        let prev = count_nonzero_up_to(a, n - 1);
        if a[(n - 1) as int] != 0 {
            prev + 1
        } else {
            prev
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i32>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by using usize consistently */
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            count <= i,
            count == count_nonzero_up_to(a, i),
            forall|j: int| 0 <= j < i && a[j] == 0 ==> count_nonzero_up_to(a, (j + 1) as usize) == count_nonzero_up_to(a, j as usize),
            forall|j: int| 0 <= j < i && a[j] != 0 ==> count_nonzero_up_to(a, (j + 1) as usize) == count_nonzero_up_to(a, j as usize) + 1
        decreases a.len() - i
    {
        if a[i] != 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    proof {
        assert(count == count_nonzero_up_to(a, a.len()));
        if a.len() > 0 {
            if forall|j: int| 0 <= j < a.len() ==> a[j] == 0 {
                assert(count_nonzero_up_to(a, a.len()) == 0);
            }
            if forall|j: int| 0 <= j < a.len() ==> a[j] != 0 {
                assert(count_nonzero_up_to(a, a.len()) == a.len());
            }
        }
    }
    count
}
// </vc-code>

}
fn main() {}