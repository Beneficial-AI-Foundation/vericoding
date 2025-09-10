use vstd::prelude::*;

verus! {

spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

fn numpy_diagonal(x: Vec<Vec<f32>>, offset: i32) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        x.len() < usize::MAX,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() == x[0].len(),
    ensures
        result.len() == spec_min(x.len() as int, x[0].len() as int),
        offset == 0 ==> forall|i: int| 0 <= i < result.len() ==> 
            result[i] == x[i][i],
        forall|i: int| 0 <= i < result.len() ==> 
            exists|r: int, c: int| 
                0 <= r < x.len() && 0 <= c < x[0].len() &&
                result[i] == x[r][c],
{
    assume(false);
    unreached()
}

}
fn main() {}