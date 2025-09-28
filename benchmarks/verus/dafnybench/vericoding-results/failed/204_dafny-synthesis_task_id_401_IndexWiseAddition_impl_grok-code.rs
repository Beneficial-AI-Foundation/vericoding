use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
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
    let mut result = seq![];
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i >= 0,
            result.len() == i,
            i <= a.len(),
            forall|k: int| 0 <= k < i as int ==> #[trigger] result[k].len() == a[k].len(),
            forall|k: int, l: int| 0 <= k < i as int && 0 <= l < result[k].len() ==> 
                #[trigger] result[k][l] == a[k][l] + b[k][l]
    {
        let mut row = seq![];
        let mut j: usize = 0;
        while j < a[i].len()
            invariant
                j >= 0,
                row.len() == j,
                forall|l: int| 0 <= l < j as int ==> #[trigger] row[l] == a[i as int][l] + b[i as int][l]
        {
            row = row.push(a[i][j] + b[i][j]);
            j = j + 1;
        }
        assert(row.len() == a[i].len());
        assert(forall|l: int| 0 <= l < row.len() ==> #[trigger] row[l] == a[i as int][l] + b[i as int][l]);
        result = result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}