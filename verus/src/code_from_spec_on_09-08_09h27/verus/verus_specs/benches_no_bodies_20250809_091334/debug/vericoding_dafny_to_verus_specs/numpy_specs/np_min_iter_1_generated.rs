use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn min(a: &[i32]) -> (res: i32)
    requires 
        a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a.len() && res == a[i] &&
        forall|j: int| 0 <= j < a.len() ==> res <= a[j],
{
    let mut min_val = a[0];
    for i in 1..a.len() {
        if a[i] < min_val {
            min_val = a[i];
        }
    }
    min_val
}

fn main() {
    let arr = [3, 1, 4, 1, 5, 9, 2, 6];
    let result = min(&arr);
    println!("Minimum value: {}", result);
}

}