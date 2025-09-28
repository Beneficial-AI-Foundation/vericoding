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
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn generate(num_rows: i8) -> (result: Vec<Vec<i8>>)
    requires num_rows >= 0
    ensures valid_pascal_triangle(result@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), num_rows as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type mismatches by using usize for loop variables and int for indexing */{
    let mut result: Vec<Vec<i8>> = Vec::new();
    if num_rows > 0 {
        let mut first_row: Vec<i8> = Vec::new();
        first_row.push(1);
        result.push(first_row);
    }
    let mut row_idx: usize = if num_rows > 0 { 1 } else { 0 };
    while row_idx < num_rows as usize
        invariant
            result.len() == row_idx,
            forall|i: int| 0 <= i < result.len() ==> result[i as int].len() == i + 1,
            forall|i: int| 0 <= i < result.len() ==> result[i as int][0] == 1 && result[i as int][result[i as int].len() - 1] == 1,
            forall|i: int, j: int| 1 <= i < result.len() && 0 < j < result[i as int].len() - 1 ==> result[i as int][j] == result[(i as int)-1][j-1] + result[(i as int)-1][j],
        decreases ((num_rows as usize) - row_idx)
    {
        let mut new_row: Vec<i8> = Vec::new();
        new_row.push(1);
        let mut j: usize = 1;
        while j < row_idx
            invariant
                new_row.len() == j && 1 <= j <= row_idx,
                new_row[0] == 1,
                forall|k: int| 1 <= k < j as int ==> new_row[k] == result[(row_idx as int) - 1][k - 1] + result[(row_idx as int) - 1][k],
            decreases ((row_idx as int) - (j as int))
        {
            let sum = result[(row_idx as int) - 1][(j as int) - 1] + result[(row_idx as int) - 1][j as int];
            new_row.push(sum);
            j += 1;
        }
        new_row.push(1);
        result.push(new_row);
        row_idx += 1;
    }
    result
}
// </vc-code>


}

fn main() {}