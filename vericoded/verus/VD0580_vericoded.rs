use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn append_array(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures 
        c.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == c[i],
        forall|i: int| 0 <= i < b.len() ==> b[i] == c[a.len() + i],
// </vc-spec>
// <vc-code>
{
    let mut c: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] c[k] == a[k],
        decreases a.len() - i
    {
        c.push(a[i]);
        i += 1;
    }

    assert(i == a.len());

    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            c.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() ==> #[trigger] c[k] == a[k],
            forall|k: int| 0 <= k < j ==> #[trigger] c[a.len() + k] == b[k],
        decreases b.len() - j
    {
        c.push(b[j]);
        j += 1;
    }

    assert(j == b.len());

    c
}
// </vc-code>

fn main() {
}

}