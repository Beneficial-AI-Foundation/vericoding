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
/* helper modified by LLM (iteration 5): fixed ghost/exec type errors. */
fn compute_cell(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, row: usize, column: usize) -> (r: int)
    requires
        m1.len() > 0,
        m2.len() > 0,
        m1[0].len() == m2.len(),
        forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1[i].len() == m1[0].len(),
        forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2[i].len() == m2[0].len(),
        row < m1.len(),
        column < m2[0].len(),
    ensures
        r as int == row_column_product(m1, m2, row as int, column as int),
{
    let mut k: usize = 0;
    let mut sum: int = 0;
    while k < m1[0].len()
        invariant
            m1.len() > 0,
            m2.len() > 0,
            m1[0].len() == m2.len(),
            forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1[i].len() == m1[0].len(),
            forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2[i].len() == m2[0].len(),
            row < m1.len(),
            column < m2[0].len(),
            k <= m1[0].len(),
            sum as int + row_column_product_from(m1, m2, row as int, column as int, k as int) == row_column_product(m1, m2, row as int, column as int),
        decreases m1[0].len() - k
    {
        let val1 = m1[row][k];
        let val2 = m2[k][column];
        sum = sum + val1 * val2;
        k = k + 1;
    }
    sum
}

/* helper modified by LLM (iteration 5): fixed ghost/exec type errors. */
fn compute_row(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, i: usize) -> (row_vec: Vec<int>)
    requires
        m1.len() > 0,
        m2.len() > 0,
        m1[0].len() == m2.len(),
        forall|k: int| 0 <= k < m1.len() ==> #[trigger] m1[k].len() == m1[0].len(),
        forall|k: int| 0 <= k < m2.len() ==> #[trigger] m2[k].len() == m2[0].len(),
        i < m1.len(),
    ensures
        row_vec.len() == m2[0].len(),
        forall|j: int| 0 <= j < row_vec.len() ==> #[trigger] row_vec@[j] as int == row_column_product(m1, m2, i as int, j),
{
    let mut j: usize = 0;
    let mut row_vec: Vec<int> = Vec::new();
    while j < m2[0].len()
        invariant
            m1.len() > 0,
            m2.len() > 0,
            m1[0].len() == m2.len(),
            forall|k: int| 0 <= k < m1.len() ==> #[trigger] m1[k].len() == m1[0].len(),
            forall|k: int| 0 <= k < m2.len() ==> #[trigger] m2[k].len() == m2[0].len(),
            i < m1.len(),
            j <= m2[0].len(),
            row_vec.len() == j,
            forall|k: int| 0 <= k < j ==> #[trigger] row_vec@[k] as int == row_column_product(m1, m2, i as int, k),
        decreases m2[0].len() - j
    {
        let cell_val = compute_cell(m1, m2, i, j);
        row_vec.push(cell_val);
        j = j + 1;
    }
    row_vec
}
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
/* code modified by LLM (iteration 5): fixed ghost/exec type errors and added sequence indexing. */
{
    let mut i: usize = 0;
    let mut m3: Vec<Vec<int>> = Vec::new();
    while i < m1.len()
        invariant
            m1.len() > 0,
            m2.len() > 0,
            m1[0].len() == m2.len(),
            forall|k: int| 0 <= k < m1.len() ==> #[trigger] m1[k].len() == m1[0].len(),
            forall|k: int| 0 <= k < m2.len() ==> #[trigger] m2[k].len() == m2[0].len(),
            i <= m1.len(),
            m3.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] m3@[k].len() == m2[0].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < m2[0].len() ==> 
                #[trigger] m3@[k]@[j] as int == row_column_product(m1, m2, k, j),
        decreases m1.len() - i
    {
        let row_vec = compute_row(m1, m2, i);
        m3.push(row_vec);
        i = i + 1;
    }
    m3
}
// </vc-code>

}
fn main() {}