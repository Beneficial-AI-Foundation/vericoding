use vstd::prelude::*;

verus! {

fn cum_prod(a: &[i32]) -> (res: Vec<i32>)
    ensures
        res.len() == a.len(),
        res.len() > 0 ==> res[0int] == a[0int],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] * a[i],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {
    // TODO: Remove this comment and implement the function body
}

}