// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn row_column_product(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, row: int, column: int) -> int
    recommends
        m1.len() > 0,
        m2.len() > 0,
        m1[0].len() == m2.len(),
        0 <= row < m1.len(),
        0 <= column < m2[0].len(),
        forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1[i].len() == m1[0].len(),
        forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2[i].len() == m2[0].len(),
{
    row_column_product_from(m1, m2, row, column, 0)
}

spec fn row_column_product_from(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, row: int, column: int, k: int) -> int
    recommends
        m1.len() > 0,
        m2.len() > 0,
        0 <= k <= m1[0].len(),
        m1[0].len() == m2.len(),
        0 <= row < m1.len(),
        0 <= column < m2[0].len(),
        forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1[i].len() == m1[0].len(),
        forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2[i].len() == m2[0].len(),
        k < m1[0].len() ==> 0 <= k < m1[row].len(),
        k < m1[0].len() ==> 0 <= k < m2.len(),
        k < m1[0].len() ==> 0 <= column < m2[k].len(),
    decreases m1[0].len() - k
    when 0 <= k <= m1[0].len()
{
    if k == m1[0].len() {
        0
    } else {
        m1[row][k] * m2[k][column] + row_column_product_from(m1, m2, row, column, k + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn multiply(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>) -> (m3: Vec<Vec<int>>)
    requires
        m1.len() > 0,
        m2.len() > 0,
        m1[0].len() == m2.len(),
        forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1[i].len() == m1[0].len(),
        forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2[i].len() == m2[0].len(),
    ensures
        m3.len() == m1.len(),
        m3.len() > 0 ==> m3[0].len() == m2[0].len(),
        forall|i: int| 0 <= i < m3.len() ==> #[trigger] m3[i].len() == m2[0].len(),
        forall|i: int, j: int| 0 <= i < m3.len() && 0 <= j < m2[0].len() ==>
            #[trigger] m3[i][j] == row_column_product(m1, m2, i, j),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}