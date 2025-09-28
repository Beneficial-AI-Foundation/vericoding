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
/* helper modified by LLM (iteration 5): fixed syntax error by adding ! for lemma declarations */
proof fn lemma_valid_empty_triangle()
    ensures valid_pascal_triangle(Seq::<Seq<int>>::empty(), 0)
{
}

proof fn lemma_valid_single_row()
    ensures valid_pascal_triangle(seq![seq![1]], 1)
{
}

proof fn lemma_pascal_property(triangle: Seq<Seq<int>>, i: nat, j: nat)
    requires
        i > 0,
        j > 0,
        i < triangle.len(),
        j < triangle[i as int].len() - 1,
        valid_pascal_triangle(triangle, i as int)
    ensures triangle[i as int][j as int] == triangle[(i-1) as int][(j-1) as int] + triangle[(i-1) as int][j as int]
{
}
// </vc-helpers>

// <vc-spec>
fn generate(num_rows: i8) -> (result: Vec<Vec<i8>>)
    requires num_rows >= 0
    ensures valid_pascal_triangle(result@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), num_rows as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): complete Pascal triangle implementation without verification bypasses */
    if num_rows == 0 {
        return Vec::new();
    }
    
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: i8 = 0;
    
    while i < num_rows
        invariant
            0 <= i <= num_rows,
            result.len() == i,
            valid_pascal_triangle(result@.map(|k, row: Vec<i8>| row@.map(|l, x: i8| x as int)), i as int)
        decreases num_rows - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: i8 = 0;
        
        while j <= i
            invariant
                0 <= j <= i + 1,
                row.len() == j,
                forall|k: int| 0 <= k < j ==> (
                    (k == 0 || k == j - 1) ==> row@[k] == 1
                ),
                forall|k: int| 1 <= k < j - 1 && i > 0 ==> (
                    row@[k] == result@[(i-1) as int]@[(k-1) as int] + result@[(i-1) as int]@[k as int]
                )
            decreases i - j + 1
        {
            if j == 0 || j == i {
                row.push(1);
            } else {
                let val = result[(i-1) as usize][j-1 as usize] + result[(i-1) as usize][j as usize];
                row.push(val);
            }
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}