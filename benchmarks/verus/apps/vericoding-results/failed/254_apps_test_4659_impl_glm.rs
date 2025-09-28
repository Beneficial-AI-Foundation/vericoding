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
/* helper modified by LLM (iteration 5): added decreases clause to loop for termination */
fn next_row(prev: Vec<i8>) -> (row: Vec<i8>)
    requires prev.len() >= 1
    ensures
        row.len() == prev.len() + 1,
        row[0] == 1,
        row[row.len()-1] == 1,
        forall|i: int| 1 <= i < row.len()-1 ==> row[i as int] == prev[i-1] + prev[i],
{
    let mut row = Vec::new();
    row.push(1);
    let mut i: usize = 1;
    while i < prev.len()
        invariant
            1 <= (i as int) <= (prev.len() as int),
            row.len() == i,
            row[0] == 1,
            forall|j: int| 0 < j < (i as int) ==> row[j] == prev[j-1] + prev[j],
        decreases prev.len() - i
    {
        row.push(prev[i-1] + prev[i]);
        i = i + 1;
    }
    row.push(1);
    row
}
// </vc-helpers>

// <vc-spec>
fn generate(num_rows: i8) -> (result: Vec<Vec<i8>>)
    requires num_rows >= 0
    ensures valid_pascal_triangle(result@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), num_rows as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to main loop for termination */
    if num_rows == 0 {
        return Vec::new();
    }
    let mut triangle = Vec::new();
    triangle.push(vec![1]);
    let mut row_index: i8 = 1;
    while row_index < num_rows
        invariant
            1 <= (row_index as int) <= (num_rows as int),
            triangle.len() == row_index as usize,
            valid_pascal_triangle(triangle@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), row_index as int)
        decreases num_rows - row_index
    {
        let prev = triangle[(row_index-1) as usize].clone();
        let next = next_row(prev);
        triangle.push(next);
        row_index = row_index + 1;
    }
    triangle
}
// </vc-code>


}

fn main() {}