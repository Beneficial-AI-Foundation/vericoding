// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn slope_search_precond(a: &Vec<Vec<i32>>, key: i32) -> bool {
    a.len() > 0 &&
    (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len()) &&
    (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() - 1 ==> #[trigger] a[i][j] <= a[i][j + 1]) &&
    (forall|j: int, i: int| 0 <= j < a[0].len() && 0 <= i < a.len() - 1 ==> #[trigger] a[i][j] <= a[i + 1][j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by removing key parameter */
proof fn lemma_search_completeness(a: &Vec<Vec<i32>>, key: i32, final_i: usize, final_j: usize)
    requires
        slope_search_precond(a, key),
        final_i == a.len() || final_j == usize::MAX,
        forall|r: int, c: int| 0 <= r < final_i && 0 <= c < a[r].len() ==> a[r][c] < key,
        final_j < a[0].len() ==> forall|r: int, c: int| 0 <= r < a.len() && final_j + 1 <= c < a[r].len() ==> a[r][c] > key
    ensures
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() ==> a[i][j] != key
{
}

proof fn lemma_bounds_preserved(a: &Vec<Vec<i32>>, key: i32, i: usize, j: usize)
    requires
        slope_search_precond(a, key),
        i < a.len(),
        j < a[0].len()
    ensures
        i < a.len(),
        j < a[i].len()
{
}
// </vc-helpers>

// <vc-spec>
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (result: (i32, i32))
    requires slope_search_precond(a, key),
    ensures
        ({
            let (m, n) = result;
            ((m >= 0 && m < a.len() && n >= 0 && n < a[0].len() && a[m as int][n as int] == key) ||
             (m == -1 && n == -1 && forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() ==> #[trigger] a[i][j] != key))
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing key parameter */
    if a.len() == 0 || a[0].len() == 0 {
        return (-1, -1);
    }
    
    let rows = a.len();
    let cols = a[0].len();
    
    let mut i: usize = 0;
    let mut j: usize = cols - 1;
    
    while i < rows && j < cols
        invariant
            i <= rows,
            j < cols || j == usize::MAX,
            rows == a.len(),
            cols == a[0].len(),
            cols > 0,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < a[r].len() ==> a[r][c] < key,
            j < cols ==> forall|r: int, c: int| 0 <= r < a.len() && j + 1 <= c < a[r].len() ==> a[r][c] > key
        decreases rows - i + (if j == usize::MAX { 0 } else { j + 1 })
    {
        if j == usize::MAX {
            break;
        }
        
        proof {
            assert(i < rows && j < cols);
            assert(i < a.len() && j < a[0].len());
            assert(forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len());
            assert(j < a[i].len());
        }
        
        let current = a[i][j];
        
        if current == key {
            proof {
                assert(i < a.len() && j < a[0].len());
                assert(a[i as int][j as int] == key);
            }
            return (i as i32, j as i32);
        } else if current < key {
            i += 1;
        } else {
            if j == 0 {
                j = usize::MAX;
            } else {
                j -= 1;
            }
        }
    }
    
    proof {
        lemma_search_completeness(a, key, i, j);
    }
    
    (-1, -1)
}
// </vc-code>

}
fn main() {}