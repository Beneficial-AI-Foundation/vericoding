use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains_intersect(a: Seq<char>, b: Set<char>, x: char)
    ensures
        a.contains(x) && b.contains(x) <==> (exists|i: int| 0 <= i < a.len() && a[i] == x && b.contains(x))
{
}

proof fn lemma_set_contains_intersection(a: Set<char>, b: Set<char>, x: char)
    ensures
        a.contains(x) && b.contains(x) <==> a.intersect(b).contains(x)
{
}

proof fn lemma_set_insert_preserves_b_contains(c: Set<char>, b: Set<char>, elem: char)
    requires
        b.contains(elem)
    ensures
        forall|x: char| c.insert(elem).contains(x) ==> b.contains(x)
{
}

proof fn lemma_seq_index_in_bounds(a: Seq<char>, i: int)
    requires
        0 <= i < a.len()
    ensures
        (i as usize) < a.len()
{
}

proof fn lemma_seq_to_int_bounds(len: usize)
    ensures
        len as int >= 0
{
}

proof fn lemma_contains_after_insert(c: Set<char>, elem: char, j: int, a: Seq<char>, b: Set<char>)
    requires
        b.contains(elem),
        forall|x: char| (exists|k: int| 0 <= k < j && a@[k] == x) && b.contains(x) <==> c.contains(x)
    ensures
        forall|x: char| (exists|k: int| 0 <= k < j+1 && a@[k] == x) && b.contains(x) <==> c.insert(elem).contains(x)
{
}
// </vc-helpers>

// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// <vc-code>
{
    let mut c: Set<char> = Set::empty();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: char| (exists|j: int| 0 <= j < i as int && a@[j] == x) && b.contains(x) <==> c.contains(x),
        decreases a.len() - i,
    {
        let elem = a[i];
        if b.contains(elem) {
            proof {
                lemma_contains_after_insert(c, elem, i as int, a, b);
            }
            c = c.insert(elem);
        }
        i = i + 1;
    }
    assert forall|x: char| a.contains(x) && b.contains(x) implies c.contains(x) by {
        lemma_seq_contains_intersect(a, b, x);
    };
    assert forall|x: char| c.contains(x) implies a.contains(x) && b.contains(x) by {
        assert(forall|x: char| c.contains(x) ==> b.contains(x));
    };
    c
}
// </vc-code>

fn main() {
}

}