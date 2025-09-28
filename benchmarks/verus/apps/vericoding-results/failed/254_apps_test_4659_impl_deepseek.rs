// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_pascal_triangle(triangle: Seq<Seq<int>>, num_rows: int) -> bool {
    triangle.len() == num_rows &&
    (num_rows == 0 ==> triangle == Seq::<Seq<int>>::empty()) &&
    (num_rows > 0 ==> (
        forall|i: int| 0 <= i < triangle.len() ==> #[trigger] triangle[i].len() == i + 1
    )) &&
    (num_rows > 0 ==> (
        forall|i: int| 0 <= i < triangle.len() ==> 
            #[trigger] triangle[i][0] == 1 && #[trigger] triangle[i][triangle[i].len() - 1] == 1
    )) &&
    (num_rows > 1 ==> (
        forall|i: int, j: int| 1 <= i < triangle.len() && 1 <= j < triangle[i].len() - 1 ==> 
            #[trigger] triangle[i][j] == triangle[i-1][j-1] + triangle[i-1][j]
    ))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed result spec to use i as parameter */
fn compute_row(prev_row: &Vec<i8>, i: i8) -> Vec<i8>
    requires
        prev_row@.len() == i as int,
        i >= 1,
        prev_row@[0] == 1,
        prev_row@[prev_row@.len() - 1] == 1,
    ensures 
        result@.len() == (i + 1) as int,
        result@[0] == 1,
        result@[result@.len() - 1] == 1,
        forall|j: int| 1 <= j < result@.len() - 1 ==> #[trigger] result@[j] == prev_row@[j-1] + prev_row@[j]
{
    let mut row = vec![1; (i + 1) as usize];
    proof {
        assert(row@.len() == (i + 1) as int);
        assert(row@[0] == 1);
        assert(row@[row@.len() - 1] == 1);
    }
    let mut j: usize = 1;
    while j < prev_row.len()
        invariant
            1 <= j <= prev_row.len(),
            forall|k: int| 1 <= k < j as int ==> #[trigger] row@[k] == prev_row@[k-1] + prev_row@[k],
        decreases prev_row.len() - j
    {
        let j_int = j;
        row[j] = prev_row[j-1] + prev_row[j];
        proof {
            assert(row@[j as int] == prev_row@[j as int-1] + prev_row@[j as int]);
        }
        j += 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn generate(num_rows: i8) -> (result: Vec<Vec<i8>>)
    requires num_rows >= 0
    ensures valid_pascal_triangle(result@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), num_rows as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed result variable name in ensures clause and proof assertions */
{
    if num_rows == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    result.push(vec![1]);
    proof {
        assert(valid_pascal_triangle(result@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), 1));
    }
    
    let mut i: i8 = 1;
    while i < num_rows
        invariant
            1 <= i <= num_rows,
            result@.len() == i as int,
            valid_pascal_triangle(result@.map(|idx, row: Vec<i8>| row@.map(|j, x: i8| x as int)), i as int)
        decreases num_rows - i
    {
        let prev_row = result.last().unwrap();
        let new_row = compute_row(prev_row, i);
        result.push(new_row);
        proof {
            assert(result@.len() == (i + 1) as int);
            assert(valid_pascal_triangle(result@.map(|idx, row: Vec<i8>| row@.map(|j, x: i8| x as int)), (i + 1) as int));
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}