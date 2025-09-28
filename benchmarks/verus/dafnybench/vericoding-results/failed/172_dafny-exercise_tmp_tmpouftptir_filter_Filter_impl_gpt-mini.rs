use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let mut s: Set<char> = Set::empty();
    while i < a.len()
        invariant { i <= a.len(); }
        invariant { forall |x: char| s.contains(x) <==> (exists |j: nat| j < i && a@[j] == x && b.contains(x)); }
        decreases a.len() - i
    {
        let ch = a@[i];
        if b.contains(ch) {
            s = s.insert(ch);
        }
        i = i + 1;
    }
    s
}
// </vc-code>

fn main() {
}

}