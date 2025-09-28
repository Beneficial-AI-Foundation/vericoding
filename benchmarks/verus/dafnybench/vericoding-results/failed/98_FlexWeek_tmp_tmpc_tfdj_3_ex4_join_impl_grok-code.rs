use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn join(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures
        a@ + b@ == c@,
        (a@ + b@).to_multiset() == c@.to_multiset(),
        a@.to_multiset().add(b@.to_multiset()) == c@.to_multiset(),
        a.len() + b.len() == c.len(),
        // Forall
        forall|i: int| 0 <= i < a.len() ==> c[i] == a[i],
        forall|i: int, j: int| 
            a.len() <= i < c.len() && 
            0 <= j < b.len() && 
            i - j == a.len() ==> c[i] == b[j],
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::<i32>::new();
    let mut idx: usize = 0;
    while idx < a.len()
        decreases (a.len() as int) - (idx as int)
        invariant 0 <= (idx as int) <= (a.len() as int)
        invariant c.len() as int == (idx as int)
        invariant forall |k: int| 0 <= k < idx as int ==> #[trigger] c@[k] == a@[k]
    {
        c.push(a[idx]);
        idx += 1;
    }
    proof {
        assert(a@ == c@);
    }
    idx = 0;
    while idx < b.len()
        decreases (b.len() as int) - (idx as int)
        invariant 0 <= (idx as int) <= (b.len() as int)
        invariant c.len() as int == (a.len() as int) + (idx as int)
        invariant a@ + b@.take(idx as int) == c@
    {
        c.push(b[idx]);
        idx += 1;
    }
    proof {
        assert(a@ + b@ == c@);
        assert((a@ + b@).to_multiset() == c@.to_multiset());
        assert(a@.to_multiset().add(b@.to_multiset()) == c@.to_multiset());
    }
    c
}
// </vc-code>

fn main() {}

}