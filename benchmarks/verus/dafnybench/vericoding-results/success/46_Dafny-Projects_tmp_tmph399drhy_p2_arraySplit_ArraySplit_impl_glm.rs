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
    let mut a = a;
    if a.len() == 0 {
        (Vec::new(), Vec::new())
    } else if a.len() == 1 {
        (a, Vec::new())
    } else {
        let second = a.split_off(1);
        (a, second)
    }
}
// </vc-code>

fn main() {
}

}