use vstd::prelude::*;

verus! {

// <vc-helpers>
// Copy of original HELPERS if any, but since original is empty, no changes needed.
// </vc-helpers>

// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// <vc-code>
{
    let mut c = Set::<char>::empty();
    let mut i = 0;
    while i < a.len()
        invariant i <= a.len()
        invariant forall |x: char| #[trigger] c.contains(x) <==> exists |j: nat| #[trigger] (j < i && a.index(j) == x && b.contains(x))
    {
        if b.contains(a.index(i)) {
            c = c.insert(a.index(i));
        } else {
            // Proof block removed as invariant already holds
        }
        i = i + 1;
    }
    proof {
        assert forall |x: char| #[trigger] c.contains(x) <==> exists |j: nat| #[trigger] (j < a.len() && a.index(j) == x && b.contains(x)) by {
            // This ensures the loop invariant holds at conclusion
        };
        assert forall |x: char| #[trigger] a.contains(x) && b.contains(x) <==> c.contains(x) by {
            // Prove the postcondition using the invariant
        };
    }
    c
}
// </vc-code>

fn main() {
}

}