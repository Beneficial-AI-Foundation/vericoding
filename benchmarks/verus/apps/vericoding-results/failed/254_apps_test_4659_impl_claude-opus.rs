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
    /* code modified by LLM (iteration 5): Fixed loop invariants and added assertions for array bounds */
    let mut triangle: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    
    while i < num_rows as usize
        invariant
            0 <= i <= num_rows as usize,
            triangle.len() == i,
            valid_pascal_triangle(triangle@.map(|k, row: Vec<i8>| row@.map(|j, x: i8| x as int)), i as int),
        decreases num_rows as usize - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        
        while j <= i
            invariant
                0 <= j <= i + 1,
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row@[k] == if k == 0 || k == i { 1 } else { (triangle@[i as int - 1][k - 1] + triangle@[i as int - 1][k]) as i8 },
                0 < i <= triangle.len(),
                i > 0 ==> triangle@[i as int - 1].len() == i,
            decreases i + 1 - j
        {
            if j == 0 || j == i {
                row.push(1i8);
            } else {
                assert(i > 0);
                assert(triangle.len() == i);
                assert(triangle@[i as int - 1].len() == i);
                assert(1 <= j < i);
                assert(0 <= j - 1 < i);
                assert(0 <= j < i);
                let prev_row = &triangle[i - 1];
                let val = prev_row[j - 1] + prev_row[j];
                row.push(val);
            }
            j = j + 1;
        }
        
        assert(row@.len() == i + 1);
        assert(row@[0] == 1);
        assert(row@[row@.len() - 1] == 1);
        
        triangle.push(row);
        i = i + 1;
    }
    
    triangle
}
// </vc-code>


}

fn main() {}