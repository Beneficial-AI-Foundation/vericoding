use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
{
    let mut result: Set<char> = Set::empty();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|x: char| result.contains(x) ==> a.subrange(0, i as int).contains(x) && b.contains(x),
            forall|x: char| a.subrange(0, i as int).contains(x) && b.contains(x) ==> result.contains(x)
    {
        let x = a@[i];
        if b.contains(x) {
            result = result.insert(x);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}