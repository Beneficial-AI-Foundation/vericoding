use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = a.len();
    let mut left = a;
    let k_usize: usize = if n == 0 { 0usize } else { 1usize };
    let mut right = left.split_off(k_usize);
    if n > 1 {
        assert(left.len() == 1);
        assert(right.len() + left.len() == n);
        assert(n > left.len());
        assert(n > right.len());
    }
    (left, right)
}
// </vc-code>

fn main() {
}

}