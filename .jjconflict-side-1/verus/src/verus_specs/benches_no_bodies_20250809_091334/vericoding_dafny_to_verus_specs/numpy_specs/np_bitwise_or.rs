use vstd::prelude::*;

verus! {

// SPEC
fn bitwise_or(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0 && #[trigger] a[i] <= 65535 && #[trigger] b[i] >= 0 && #[trigger] b[i] <= 65535,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == ((a[i] as u16) | (b[i] as u16)) as i32,
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

// SPEC
fn bitwise_or_prime(a: &[u32], b: &[u32]) -> (res: Vec<i32>)
    requires
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == (a[i] | b[i]) as i32,
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}

fn main() {}