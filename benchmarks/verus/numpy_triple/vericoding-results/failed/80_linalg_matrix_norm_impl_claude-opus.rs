// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn matrix_norm(x: Vec<Vec<i8>>) -> (result: i8)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() == x@[0].len(),
    ensures
        result as int >= 0,
        (result as int == 0) == (forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> #[trigger] x@[i][j] == 0),
        forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> abs_val(#[trigger] x@[i][j] as int) <= result as int,
        (exists|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() && #[trigger] x@[i][j] != 0) ==> result as int > 0,
// </vc-spec>
// <vc-code>
{
    let mut max_val: i8 = 0;
    let mut found_nonzero = false;
    
    for i in 0..x.len()
        invariant
            0 <= i <= x.len(),
            x@.len() > 0,
            forall|k: int| 0 <= k < x@.len() ==> #[trigger] x@[k].len() > 0,
            forall|k: int| 0 <= k < x@.len() ==> #[trigger] x@[k].len() == x@[0].len(),
            max_val >= 0,
            forall|a: int, b: int| 0 <= a < i && 0 <= b < x@[a].len() ==> abs_val(#[trigger] x@[a][b] as int) <= max_val as int,
            found_nonzero == exists|a: int, b: int| 0 <= a < i && 0 <= b < x@[a].len() && #[trigger] x@[a][b] != 0,
            (max_val as int == 0) == !found_nonzero,
    {
        for j in 0..x[i].len()
            invariant
                0 <= i < x.len(),
                0 <= j <= x@[i as int].len(),
                x@.len() > 0,
                forall|k: int| 0 <= k < x@.len() ==> #[trigger] x@[k].len() > 0,
                forall|k: int| 0 <= k < x@.len() ==> #[trigger] x@[k].len() == x@[0].len(),
                max_val >= 0,
                forall|a: int, b: int| 0 <= a < i && 0 <= b < x@[a].len() ==> abs_val(#[trigger] x@[a][b] as int) <= max_val as int,
                forall|b: int| 0 <= b < j ==> abs_val(#[trigger] x@[i as int][b] as int) <= max_val as int,
                found_nonzero == exists|a: int, b: int| (0 <= a < i && 0 <= b < x@[a].len() || a == i && 0 <= b < j) && #[trigger] x@[a][b] != 0,
                (max_val as int == 0) == !found_nonzero,
        {
            let val = x[i][j];
            if val != 0 {
                found_nonzero = true;
                let abs_v = if val >= 0 { val } else { -val };
                if abs_v > max_val {
                    max_val = abs_v;
                }
            }
        }
    }
    
    max_val
}
// </vc-code>


}
fn main() {}