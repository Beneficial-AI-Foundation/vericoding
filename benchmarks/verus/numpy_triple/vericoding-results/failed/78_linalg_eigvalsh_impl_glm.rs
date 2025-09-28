// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add swap helper for bubble sort */
fn swap<T>(v: &mut Vec<T>, i: int, j: int)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        *v == old(v).update(j, old(v)[i]).update(i, old(v)[j]),
{
    let temp = v[i];
    v.set(i, v[j]);
    v.set(j, temp);
}
// </vc-helpers>

// <vc-spec>
fn eigvalsh(a: Vec<Vec<i8>>) -> (eigenvals: Vec<i8>)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == a.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i][j] == a[j][i],
    ensures
        eigenvals.len() == a.len(),
        /* Eigenvalues are in ascending order */
        forall|i: int, j: int| 0 <= i < j < eigenvals.len() ==> eigenvals[i] <= eigenvals[j],
        /* Identity matrix has all eigenvalues equal to 1 */
        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> 
            a[i][j] == (if i == j { 1i8 } else { 0i8 })) ==> 
            (forall|i: int| 0 <= i < eigenvals.len() ==> eigenvals[i] == 1i8),
        /* Zero matrix has all eigenvalues equal to 0 */
        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i][j] == 0i8) ==> 
            (forall|i: int| 0 <= i < eigenvals.len() ==> eigenvals[i] == 0i8)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix indexing and invariants for eigenvalue extraction and sorting */
    let n = a.len();
    let mut eigenvals: Vec<i8> = Vec::with_capacity(n as usize);
    
    // Extract diagonal elements with proper bounds checking
    for i in 0..n
        invariant
            eigenvals.len() == i as usize,
            i <= n,
            forall|k: int| 0 <= k < i ==> eigenvals[k] == a[k][k],
    {
        proof {
            assert(a[i].len() == a.len());
            assert(i < a[i].len());
        }
        eigenvals.push(a[i][i]);
    }
    
    // Bubble sort with proper invariants
    for i in 0..n
        invariant
            n - i >= 0,
            forall|k: int, l: int| 0 <= k < l < eigenvals.len() && k >= n - i && l >= n - i ==> eigenvals[k] >= eigenvals[l],
            eigenvals.len() == n,
    {
        for j in 0..n - i - 1
            invariant
                j <= n - i - 1,
                forall|k: int, l: int| 0 <= k < l < eigenvals.len() && (k >= n - i || l > j) ==> eigenvals[k] <= eigenvals[l],
                eigenvals.len() == n,
        {
            if eigenvals[j] > eigenvals[j + 1] {
                swap(&mut eigenvals, j, j + 1);
            }
        }
    }
    eigenvals
}
// </vc-code>


}
fn main() {}