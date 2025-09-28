// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn spec_get_col(m: Seq<Seq<i8>>, j: int) -> Seq<i8>
{
    Seq::new(m.len(), |i: int| m[i][j])
}

/* helper modified by LLM (iteration 3): fixed wrong lambda arity in map call */
fn get_col(m: &Vec<Vec<i8>>, j: usize) -> (col: Vec<i8>)
    requires
        m.len() > 0,
        j < m.len(),
        forall|i: int| 0 <= i < m.len() ==> m@[i].len() == m.len(),
    ensures
        col.len() == m.len(),
        col@ == spec_get_col(m@.map(|_idx, r: Vec<i8>| r@), j as int),
{
    let mut col = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            m.len() > 0,
            j < m.len(),
            forall|k: int| 0 <= k < m.len() ==> m@[k].len() == m.len(),
            0 <= i <= m.len(),
            col.len() == i,
            col@ == spec_get_col(m@.map(|_idx, r: Vec<i8>| r@), j as int).take(i as int),
        decreases m.len() - i
    {
        col.push(m[i][j]);
        i = i + 1;
    }
    col
}
// </vc-helpers>

// <vc-spec>
fn matrix_power(a: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() == a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i].len() == a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed wrong lambda arity in map call */
    let n = a.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            n > 0,
            forall|k: int| 0 <= k < n ==> a@[k].len() == n,
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k].len() == n,
            forall|k: int| 0 <= k < i ==> result@[k]@ == spec_get_col(a@.map(|_idx, r: Vec<i8>| r@), k as int),
        decreases n - i
    {
        let new_row = get_col(&a, i);
        result.push(new_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}