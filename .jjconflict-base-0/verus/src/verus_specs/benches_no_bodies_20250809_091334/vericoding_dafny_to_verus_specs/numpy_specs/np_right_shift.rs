use vstd::prelude::*;

verus! {

fn right_shift(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 65535,
        forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 16,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == ((#[verifier::truncate] (a[i] as u16)) >> (#[verifier::truncate] (b[i] as u16))) as i32,
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}

fn main() {}