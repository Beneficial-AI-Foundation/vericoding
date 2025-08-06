use vstd::arithmetic::mul::*;
use vstd::math::abs;
use vstd::prelude::*;

verus! {

proof fn lemma_cube_increases_helper(i: int)
    // post-conditions-start
    ensures
        i >= 0 ==> (i * i * i) <= (i + 1) * (i + 1) * (i + 1),
    // post-conditions-end
{
    // impl-start
    broadcast use group_mul_properties;

    if (i > 0) {
        assert((i + 1) * (i + 1) * (i + 1) == i * i * i + 3 * i * i + 3 * i + 1); // assert-line
        assert(i * i * i + 3 * i * i + 3 * i + 1 > i * i * i); // assert-line
    }
    // impl-end
}
// pure-end

proof fn lemma_cube_increases_params(i: int, j: int)
    // post-conditions-start
    ensures
        0 <= i <= j ==> (i * i * i) <= (j * j * j),
    // post-conditions-end
    decreases j - i,
{
    // impl-start
    if (i == j) {
    }
     else if (i < j) {
        lemma_cube_increases_params(i, j - 1);
        lemma_cube_increases_helper(j - 1);

    }
    // impl-end
}
// pure-end

proof fn lemma_cube_increases()
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i <= j ==> #[trigger] (i * i * i) <= #[trigger] (j * j * j),
    // post-conditions-end
{
    // impl-start
    assert forall|i: int, j: int|
        0 <= i <= j ==> #[trigger] (i * i * i) <= #[trigger] (j * j * j) by {
        lemma_cube_increases_params(i, j);
    }
    // impl-end
}
// pure-end

fn checked_cube(x: i32) -> (ret: Option<i32>)
    // pre-conditions-start
    requires
        x >= 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret.is_some() ==> ret.unwrap() == x * x * x,
        ret.is_none() ==> x * x * x > i32::MAX,
    // post-conditions-end
{
    let cube = (x as i64) * (x as i64) * (x as i64);
    if cube <= i32::MAX as i64 {
        Some(cube as i32)
    } else {
        None
    }
}

#[verifier::external_fn_specification]
/* code modified by LLM (iteration 1): added pub visibility to match external_fn_specification requirement */
pub fn ex_abs(x: i32) -> (ret: i32)
    requires
        x != i32::MIN,

    ensures
        ret == abs(x as int),
{
    x.abs()
}

fn is_cube(x: i32) -> (ret: bool)
    // pre-conditions-start
    requires
        x != i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret <==> exists|i: int| 0 <= i && abs(x as int) == #[trigger] (i * i * i),
    // post-conditions-end
{
    proof {
        lemma_cube_increases();
    }
    
    let abs_x = ex_abs(x);
    let mut i: i32 = 0;
    
    while i <= 1290
        invariant
            0 <= i <= 1291,
            abs_x == abs(x as int),
            forall|j: int| 0 <= j < i ==> j * j * j < abs_x,
            i > 1290 ==> abs_x > 1290 * 1290 * 1290,
    {
        let cube_opt = checked_cube(i);
        if cube_opt.is_some() {
            let cube = cube_opt.unwrap();
            if cube == abs_x {
                return true;
            } else if cube > abs_x {
                return false;
            }
        } else {
            return false;
        }
        i = i + 1;
    }
    false
}

}
fn main() {}