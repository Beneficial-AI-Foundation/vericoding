use vstd::prelude::*;

verus! {

fn divmod(x1: Vec<i32>, x2: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures ({
        let (quotient, remainder) = result;
        quotient.len() == x1.len() &&
        remainder.len() == x1.len() &&
        forall|i: int| 0 <= i < x1.len() ==> {
            x1[i] == x2[i] * quotient[i] + remainder[i] &&
            (x2[i] > 0 ==> 0 <= remainder[i] && remainder[i] < x2[i]) &&
            (x2[i] < 0 ==> x2[i] < remainder[i] && remainder[i] <= 0)
        }
    })
{
    assume(false);
    unreached()
}

}
fn main() {}