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
/* helper modified by LLM (iteration 5): convert sequence of Vec<i8> to sequence of Seq<int> */
spec fn vecs_to_int_seq(v: Seq<Vec<i8>>) -> Seq<Seq<int>> {
    v.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int))
}

/* helper modified by LLM (iteration 5): relate lengths between Vec and mapped Seq */
proof fn vecs_to_int_seq_row_len(v: Seq<Vec<i8>>, idx: int)
    requires 0 <= idx && idx < v.len(),
    ensures vecs_to_int_seq(v)[idx].len() == (v[idx])@.len(),
{
    // By definition of vecs_to_int_seq and properties of map, the mapped row has same length as original row
    assert(vecs_to_int_seq(v) == v.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)));
    assert(vecs_to_int_seq(v)[idx] == (v[idx])@.map(|j, x: i8| x as int));
    assert(vecs_to_int_seq(v)[idx].len() == (v[idx])@.len());
}

// </vc-helpers>

// <vc-spec>
fn generate(num_rows: i8) -> (result: Vec<Vec<i8>>)
    requires num_rows >= 0
    ensures valid_pascal_triangle(result@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), num_rows as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build Pascal's triangle with explicit proofs for safe indexing and maintaining invariant */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0usize;
    let n: usize = num_rows as usize;
    while i < n
        invariant
            result.len() == i,
            valid_pascal_triangle(vecs_to_int_seq(result@), i as int),
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        if i == 0 {
            row.push(1i8);
        } else {
            let prev_row: Vec<i8> = result[i - 1].clone();
            let prev_len: usize = prev_row.len();
            proof {
                assert(i > 0);
                assert(result@.len() == i as int);
                vecs_to_int_seq_row_len(result@, (i as int) - 1);
                assert(vecs_to_int_seq(result@)[(i as int) - 1].len() == i as int);
                assert(prev_row@.len() == i as int);
                assert(prev_row@.len() == prev_len as int);
            }
            // left boundary
            row.push(1i8);
            // inner elements
            let mut j: usize = 1usize;
            while j < prev_len
                invariant
                    1usize <= j && j <= prev_len,
                decreases prev_len - j
            {
                let a: i8 = prev_row[j - 1];
                let b: i8 = prev_row[j];
                let s: i8 = a + b;
                row.push(s);
                j = j + 1usize;
            }
            // right boundary
            row.push(1i8);
            proof {
                assert(prev_len as int == i as int);
                assert(row@.len() == (i as int) + 1);
                assert(row@[0] == 1);
                assert(row@[row@.len() - 1] == 1);
                let mut k: usize = 1usize;
                while k < prev_len
                    invariant
                        1usize <= k && k <= prev_len,
                    decreases prev_len - k
                {
                    assert((row@[k as int] as int) == ((prev_row@[(k - 1) as int] as int) + (prev_row@[k as int] as int)));
                    k = k + 1usize;
                }
            }
        }
        result.push(row.clone());
        proof {
            assert(vecs_to_int_seq(result@).len() == (i as int) + 1);
        }
        i = i + 1usize;
    }
    result
}

// </vc-code>


}

fn main() {}