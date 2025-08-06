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
    return None;  // TODO: Remove this line and implement the function body
}

#[verifier::external_fn_specification]
fn ex_abs(x: i32) -> (ret: i32)
    requires
        x != i32::MIN,

    ensures
        ret == abs(x as int),
{
    return 0;  // TODO: Remove this line and implement the function body
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
    return false;  // TODO: Remove this line and implement the function body
}

}
fn main() {}
