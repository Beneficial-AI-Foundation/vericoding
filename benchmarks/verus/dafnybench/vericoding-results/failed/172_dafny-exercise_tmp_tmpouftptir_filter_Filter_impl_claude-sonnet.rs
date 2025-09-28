use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// <vc-code>
{
    let mut result = Set::empty();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: char| result.contains(x) ==> (a.contains(x) && b.contains(x)),
            forall|x: char| (exists|j: int| 0 <= j < i && a[j] == x) && b.contains(x) ==> result.contains(x)
    {
        let ch = a[i as usize];
        if b.contains(ch) {
            result = result.insert(ch);
        }
        i = i + 1;
    }
    
    assert(forall|x: char| result.contains(x) ==> (a.contains(x) && b.contains(x)));
    assert(forall|x: char| (a.contains(x) && b.contains(x)) ==> result.contains(x)) by {
        assert(forall|x: char| a.contains(x) ==> (exists|j: int| 0 <= j < a.len() && a[j] == x));
    };
    
    result
}
// </vc-code>

fn main() {
}

}