use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn index_wise_addition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires 
        a.len() > 0 && b.len() > 0,
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == b[i].len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == a[i].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == a[i][j] + b[i][j],
// </vc-spec>
// <vc-code>
{
    Seq::new(a.len(), |i: int| {
        assert(0 <= i && i < a.len());
        let row_a = a.index(i);
        let row_b = b.index(i);
        assert(row_a.len() == row_b.len());
        let row_len = row_a.len();
        Seq::new(row_len, |j: int| {
            assert(0 <= j && j < row_len);
            row_a.index(j) + row_b.index(j)
        })
    })
}
// </vc-code>

fn main() {}

}