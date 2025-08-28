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
proof fn lemma_row_column_product_from_base(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, row: int, column: int)
    requires
        m1.len() > 0,
        m2.len() > 0,
        m1@[0].len() == m2.len(),
        0 <= row < m1.len(),
        0 <= column < m2@[0].len(),
        forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1@[i].len() == m1@[0].len(),
        forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2@[i].len() == m2@[0].len(),
    ensures
        row_column_product_from(m1, m2, row, column, m1@[0].len() as int) == 0
{}

proof fn lemma_row_column_product_invariant(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, row: int, column: int, k: int)
    requires
        m1.len() > 0,
        m2.len() > 0,
        0 <= k < m1@[0].len(),
        m1@[0].len() == m2.len(),
        0 <= row < m1.len(),
        0 <= column < m2@[0].len(),
        forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1@[i].len() == m1@[0].len(),
        forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2@[i].len() == m2@[0].len(),
    ensures
        0 <= k < m1@[row].len(),
        0 <= k < m2.len(),
        0 <= column < m2@[k].len(),
{}

proof fn lemma_matrix_bounds(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, i: usize, j: usize)
    requires
        m1.len() > 0,
        m2.len() > 0,
        m1@[0].len() == m2.len(),
        forall|k: int| 0 <= k < m1.len() ==> #[trigger] m1@[k].len() == m1@[0].len(),
        forall|k: int| 0 <= k < m2.len() ==> #[trigger] m2@[k].len() == m2@[0].len(),
        i < m1.len(),
        j < m2@[0].len(),
    ensures
        0 <= i < m1.len(),
        0 <= j < m2@[0].len(),
        m1@[i].len() == m1@[0].len(),
{}

proof fn lemma_row_column_product_compute(
    m1: &Vec<Vec<int>>, 
    m2: &Vec<Vec<int>>, 
    row: usize, 
    column: usize,
    computed_value: int
)
    requires
        m1.len() > 0,
        m2.len() > 0,
        m1@[0].len() == m2.len(),
        forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1@[i].len() == m1@[0].len(),
        forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2@[i].len() == m2@[0].len(),
        row < m1.len(),
        column < m2@[0].len(),
        computed_value == row_column_product_from(m1, m2, row as int, column as int, 0),
    ensures
        computed_value == row_column_product(m1, m2, row as int, column as int),
{}

fn compute_row_column_product(m1: &Vec<Vec<int>>, m2: &Vec<Vec<int>>, row: usize, column: usize) -> (result: int)
    requires
        m1.len() > 0,
        m2.len() > 0,
        m1@[0].len() == m2.len(),
        forall|i: int| 0 <= i < m1.len() ==> #[trigger] m1@[i].len() == m1@[0].len(),
        forall|i: int| 0 <= i < m2.len() ==> #[trigger] m2@[i].len() == m2@[0].len(),
        row < m1.len(),
        column < m2@[0].len(),
    ensures
        result == row_column_product(m1, m2, row as int, column as int),
{
    let mut sum = 0;
    let mut k = 0;
    
    while k < m1@[0].len()
        invariant
            k <= m1@[0].len(),
            sum == row_column_product_from(m1, m2, row as int, column as int, k as int),
    {
        proof {
            lemma_row_column_product_invariant(m1, m2, row as int, column as int, k as int);
        }
        sum = sum + m1@[row]@[k] * m2@[k]@[column];
        k = k + 1;
    }
    
    proof {
        lemma_row_column_product_compute(m1, m2, row, column, sum);
    }
    
    sum
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
{
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < m1.len()
        invariant
            i <= m1.len(),
            result.len() == i,
            forall|r: int| 0 <= r < i ==> #[trigger] result@[r].len() == m2@[0].len(),
            forall|r: int, c: int| 0 <= r < i && 0 <= c < m2@[0].len() ==>
                #[trigger] result@[r]@[c] == row_column_product(m1, m2, r, c),
    {
        let mut row = Vec::new();
        let mut j = 0;
        
        while j < m2@[0].len()
            invariant
                j <= m2@[0].len(),
                row.len() == j,
                forall|c: int| 0 <= c < j ==> 
                    #[trigger] row@[c] == row_column_product(m1, m2, i as int, c),
        {
            proof {
                lemma_matrix_bounds(m1, m2, i, j);
            }
            let product = compute_row_column_product(m1, m2, i, j);
            row.push(product);
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