// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Sum of integers over finite indices */
pub open spec fn int_sum(n: nat, f: spec_fn(int) -> int) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        f((n - 1) as int) + int_sum((n - 1) as nat, f)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ifftn(a: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires 
        a.len() > 0,
        a.len() < usize::MAX,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() < usize::MAX,
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() ==> a@[i].len() == a@[j].len(),
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == a@[0].len(),
        forall|i: int, j: int| #[trigger] result@[i][j] == 0 || 
            (0 <= i < result@.len() && 0 <= j < result@[i].len()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix compilation error */
    let n = a.len();
    let m = a[0].len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result@.len() == i,
            n == a@.len(),
            m == a@[0].len(),
            forall|k: int| 0 <= k < i ==> result@[k].len() == m,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < m ==> result@[k][j] == 0,
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        
        while j < m
            invariant
                j <= m,
                row@.len() == j,
                m == a@[0].len(),
                forall|k: int| 0 <= k < j ==> row@[k] == 0,
            decreases m - j
        {
            row.push(0i8);
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