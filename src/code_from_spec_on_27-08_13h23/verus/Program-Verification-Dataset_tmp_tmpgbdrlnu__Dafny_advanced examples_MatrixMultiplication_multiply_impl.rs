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

// <vc-helpers>
proof fn lemma_row_column_product_from(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, row: int, column: int, k: int)
    requires
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
    ensures
        row_column_product_from(m1, m2, row, column, k) == row_column_product_from(m1, m2, row, column, k)
{
    if k == m1[0].len() {
    } else {
        lemma_row_column_product_from(m1, m2, row, column, k + 1);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
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
{
    let mut result: Vec<Vec<int>> = Vec::new();
    let mut i: usize = 0;

    while i < m1.len()
        invariant
            0 <= i <= m1.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == m2[0].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < m2[0].len() ==>
                #[trigger] result[k][j] == row_column_product(m1, m2, k, j),
    {
        let mut row: Vec<int> = Vec::new();
        let mut j: usize = 0;

        while j < m2[0].len()
            invariant
                0 <= j <= m2[0].len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> #[trigger] row[k] == row_column_product(m1, m2, i as int, k),
        {
            let mut sum: int = 0;
            let mut k: usize = 0;

            while k < m1[0].len()
                invariant
                    0 <= k <= m1[0].len(),
                    sum == row_column_product_from(m1, m2, i as int, j as int, k as int),
            {
                sum = sum + m1[i][k] * m2[k][j];
                k = k + 1;
            }

            proof {
                lemma_row_column_product_from(m1, m2, i as int, j as int, 0);
            }

            row.push(sum);
            j = j + 1;
        }

        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {
}

}