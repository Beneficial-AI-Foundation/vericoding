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
/* helper modified by LLM (iteration 5): provide conversions from Seq<i8> to Seq<int> for clarity */
spec fn to_int_row(row: Seq<i8>) -> Seq<int> { row.map(|j, x: i8| x as int) }

/* helper modified by LLM (iteration 5): provide triangle-level conversion helper */
spec fn to_int_triangle(tri: Seq<Seq<i8>>) -> Seq<Seq<int>> { tri.map(|i, row: Seq<i8>| to_int_row(row)) }
// </vc-helpers>

// <vc-spec>
fn generate(num_rows: i8) -> (result: Vec<Vec<i8>>)
    requires num_rows >= 0
    ensures valid_pascal_triangle(result@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), num_rows as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix parsing by avoiding parentheses around res@ with . and improve proof bounds */
    let mut res: Vec<Vec<i8>> = Vec::new();
    let mut i: i8 = 0;
    while i < num_rows
        invariant
            0 <= i as int <= num_rows as int,
            res@.len() == i as int,
            forall|r: int| 0 <= r < res@.len() ==> res@[r]@.len() == r + 1,
            forall|r: int| 0 <= r < res@.len() ==> res@[r]@[0] as int == 1 && res@[r]@[res@[r]@.len() - 1] as int == 1,
            forall|r: int, j: int|
                1 <= r < res@.len() && 1 <= j < res@[r]@.len() - 1 ==> res@[r]@[j] as int == res@[r-1]@[j-1] as int + res@[r-1]@[j] as int,
        decreases num_rows as int - i as int
    {
        let mut row: Vec<i8> = Vec::new();
        row.push(1i8);
        if i >= 1 {
            let mut j: i8 = 1;
            while j < i
                invariant
                    1 <= j as int <= i as int,
                    row@.len() == j as int,
                    row@[0] as int == 1,
                    forall|k: int| 1 <= k < row@.len() ==> row@[k] as int == res@[(i as int - 1)]@[k-1] as int + res@[(i as int - 1)]@[k] as int,
                    res@.len() == i as int,
                    res@[(i as int - 1)]@.len() == i as int,
                decreases i as int - j as int
            {
                proof {
                    assert(0 <= (i - 1) as int);
                    assert((i - 1) as int < res@.len());
                    assert(0 <= (j - 1) as int);
                    assert((j - 1) as int < res@[(i as int - 1)]@.len());
                    assert(0 <= j as int);
                    assert(j as int < res@[(i as int - 1)]@.len());
                }
                let a = res[(i - 1) as usize][(j - 1) as usize];
                let b = res[(i - 1) as usize][j as usize];
                let s = a + b;
                row.push(s);
                j = j + 1;
            }
            row.push(1i8);
        }
        res.push(row);
        i = i + 1;
    }
    res
}
// </vc-code>


}

fn main() {}