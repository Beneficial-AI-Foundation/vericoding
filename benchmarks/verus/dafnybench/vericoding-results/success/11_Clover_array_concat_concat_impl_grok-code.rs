use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn concat(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures 
        c.len() == b.len() + a.len(),
        forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
        forall|k: int| 0 <= k < b.len() ==> c[k + a.len()] == b[k],
// </vc-spec>
// <vc-code>
{
    let mut c: Vec<i32> = Vec::new();

    for i in 0..a.len() 
        invariant
            c@.len() == i as int,
            forall |k: int| 0 <= k < i ==> #[trigger] c@[k] == a@[k],
    {
        c.push(a[i]);
    }

    for i in 0..b.len() 
        invariant
            c@.len() == a.len() as int + i as int,
            forall |k: int| 0 <= k < a.len() ==> #[trigger] c@[k] == a@[k],
            forall |k: int| 0 <= k < i ==> #[trigger] c@[k + a.len()] == b@[k],
    {
        c.push(b[i]);
    }

    c
}
// </vc-code>

fn main() {
}

}