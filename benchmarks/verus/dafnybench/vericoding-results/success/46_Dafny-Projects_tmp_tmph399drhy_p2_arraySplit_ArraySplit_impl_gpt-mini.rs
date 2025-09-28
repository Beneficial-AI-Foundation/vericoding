use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn array_split(a: Vec<i32>) -> (ret: (Vec<i32>, Vec<i32>))
    ensures
        a@ == ret.0@ + ret.1@,
        a.len() == ret.0.len() + ret.1.len(),
        a.len() > 1 ==> a.len() > ret.0.len(),
        a.len() > 1 ==> a.len() > ret.1.len(),
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 {
        (Vec::new(), Vec::new())
    } else {
        let mut left = a.clone();
        let right = left.split_off(1);
        proof {
            assert(a@ == left@ + right@);
            assert(a@.len() == left.len() + right.len());
            if a@.len() > 1 {
                assert(a@.len() > left.len());
                assert(a@.len() > right.len());
            }
        }
        (left, right)
    }
}
// </vc-code>

fn main() {
}

}