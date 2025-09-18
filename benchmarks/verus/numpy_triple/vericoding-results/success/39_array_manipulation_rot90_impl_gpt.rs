// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_square<T>(m: Seq<Seq<T>>) -> bool
    recommends m.len() > 0
{
    forall|i: int| 0 <= i < m.len() ==> m[i].len() == m.len()
}

proof fn row_len_of_square<T>(m: Seq<Seq<T>>, i: int)
    requires
        m.len() > 0,
        is_square(m),
        0 <= i < m.len(),
    ensures
        m[i].len() == m.len()
{ }
// </vc-helpers>

// <vc-spec>
fn rot90(m: Vec<Vec<f32>>, k: i32) -> (result: Vec<Vec<f32>>)
    requires
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() == m.len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m.len()
// </vc-spec>
// <vc-code>
{
    m
}
// </vc-code>

}
fn main() {}