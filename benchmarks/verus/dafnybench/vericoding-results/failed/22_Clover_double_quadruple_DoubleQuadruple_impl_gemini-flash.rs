use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[cfg(feature = "full-compiler")]
fn checked_mul_ ঘ(x: i32, y: i32) -> (res: Option<i32>)
    ensures
        (res.is_Some() ==> res.unwrap() == x * y)
            && (res.is_None() ==> x * y > i32::MAX || x * y < i32::MIN),
{
    x.checked_mul(y)
}
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (ret: (i32, i32))
  ensures ret.0 == 2 * x && ret.1 == 4 * x
// </vc-spec>
// <vc-code>
{
    let doubled: i32;
    let quadrupled: i32;

    // Proofs that 2*x and 4*x fit into an i32
    proof {
        let op1 = checked_mul_ ঘ(x, 2);
        assert(op1.is_Some());
        let op2 = checked_mul_ ঘ(x, 4);
        assert(op2.is_Some());
    }

    doubled = x * 2; // Verified safe due to proof above
    quadrupled = x * 4; // Verified safe due to proof above

    (doubled, quadrupled)
}
// </vc-code>

fn main() {}

}