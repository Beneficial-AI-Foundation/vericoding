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
fn make_zero_vec(n: usize) -> (v: Vec<i8>)
    requires
        n < usize::MAX,
    ensures
        v@.len() == n,
        forall|j:int| 0 <= j < n as int ==> v@[j] == 0,
{
    let mut v: Vec<i8> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            v.len() == k,
            k <= n,
            forall|j:int| 0 <= j < v@.len() ==> v@[j] == 0,
        decreases n - k
    {
        v.push(0i8);
        k = k + 1;
    }
    v
}

fn make_zero_matrix(rows: usize, cols: usize) -> (m: Vec<Vec<i8>>)
    requires
        rows < usize::MAX,
        cols < usize::MAX,
    ensures
        m@.len() == rows,
        forall|i:int| 0 <= i < rows as int ==> m@[i].len() == cols,
        forall|i:int, j:int| 0 <= i < rows as int && 0 <= j < cols as int ==> m@[i][j] == 0,
{
    let mut m: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            m.len() == i,
            i <= rows,
            forall|p:int| 0 <= p < m@.len() ==> m@[p].len() == cols,
            forall|p:int, q:int| 0 <= p < m@.len() && 0 <= q < m@[p].len() ==> m@[p][q] == 0,
        decreases rows - i
    {
        let row = make_zero_vec(cols);
        m.push(row);
        i = i + 1;
    }
    m
}
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
    let rows = a.len();
    let cols = a[0].len();
    let result = make_zero_matrix(rows, cols);
    result
}
// </vc-code>


}
fn main() {}