use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut s: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            s.len() == i as int,
            forall|j: int| 0 <= j && j < i as int ==> #[trigger] s[j] == a[j],
        decreases a.len() - i
    {
        let ai = a[i];
        s.push(ai);
        i += 1;
    }
    s
}
// </vc-code>

fn main() {
}

}