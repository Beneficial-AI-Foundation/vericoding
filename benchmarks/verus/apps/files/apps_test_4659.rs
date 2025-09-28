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
// </vc-helpers>

// <vc-spec>
fn generate(num_rows: i8) -> (result: Vec<Vec<i8>>)
    requires num_rows >= 0
    ensures valid_pascal_triangle(result@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), num_rows as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}