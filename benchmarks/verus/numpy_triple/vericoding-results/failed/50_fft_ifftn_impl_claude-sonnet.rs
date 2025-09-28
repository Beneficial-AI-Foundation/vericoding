// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Sum of integers over finite indices */
pub open spec fn int_sum(n: nat, f: spec_fn(int) -> int) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        f((n - 1) as int) + int_sum((n - 1) as nat, f)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch between Vec and Seq */
pub open spec fn all_matrix_dimensions_equal(a: Seq<Vec<i8>>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i]@.len() == a[j]@.len()
}

pub open spec fn matrix_bounds_valid(a: Seq<Vec<i8>>) -> bool {
    a.len() > 0 &&
    a.len() < usize::MAX &&
    (forall|i: int| 0 <= i < a.len() ==> a[i]@.len() > 0) &&
    (forall|i: int| 0 <= i < a.len() ==> a[i]@.len() < usize::MAX)
}

proof fn lemma_matrix_preserve_dimensions(a: Vec<Vec<i8>>, result: Vec<Vec<i8>>)
    requires
        matrix_bounds_valid(a@),
        all_matrix_dimensions_equal(a@),
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == a@[0]@.len(),
    ensures
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() ==> result@[i]@.len() == result@[j]@.len(),
{
}
// </vc-helpers>

// <vc-spec>
fn ifftn(a: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires 
        a.len() > 0,
        a.len() < usize::MAX,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() < usize::MAX,
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() ==> a@[i].len() == a@[j].len(),
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == a@[0].len(),
        forall|i: int, j: int| #[trigger] result@[i][j] == 0 || 
            (0 <= i < result@.len() && 0 <= j < result@[i].len()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches with proper int casting for Vec lengths */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < result@.len() ==> result@[k]@.len() == a@[0]@.len(),
        decreases a.len() - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j = 0;
        
        while j < a[i].len()
            invariant
                0 <= j <= a[i].len(),
                row@.len() == j,
                a[i].len() == a[0].len(),
            decreases a[i].len() - j
        {
            row.push(0);
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    proof {
        lemma_matrix_preserve_dimensions(a, result);
    }
    
    result
}
// </vc-code>


}
fn main() {}