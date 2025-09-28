use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains_duplicate<T: PartialEq>(s: &Seq<T>) -> (b: bool)
    ensures
        b == exists|i: int, j: int| 0 <= i < j < s.len() && s.index(i) == s.index(j)
{
    let mut i: int = 0;
    let mut b_local = false; // Introduce a local variable to hold the boolean state
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            b_local == exists|x: int, y: int| 0 <= x < y < i && s.index(x) == s.index(y),
            // b tracks b_local is not needed as b is the return value of the function
    {
        let mut j: int = i + 1;
        while j < s.len()
            invariant
                i < j <= s.len(),
                0 <= i < s.len(),
                b_local == (exists|x: int, y: int| 0 <= x < y < i && s.index(x) == s.index(y)) || (exists|y: int| i < y < j && s.index(i) == s.index(y)),
                // b tracks b_local is not needed here
        {
            if s.index(i) == s.index(j) {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}

// Proves that if a sequence has unique elements, elements added from another unique sequence
// that are not already present will maintain uniqueness.
proof fn uniqueness_preservation(s: Seq<int>, x: int, b_contains_x: bool)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s.index(i) != s.index(j),
        s.contains(x) == b_contains_x,
    ensures
        (!b_contains_x) ==> (forall|i: int, j: int| 0 <= i < j < s.push(x).len() ==> s.push(x).index(i) != s.push(x).index(j)),
{
    if !b_contains_x {
        assert(s.push(x).len() == s.len() + 1);
        assert forall|i: int, j: int| 0 <= i < j < s.push(x).len() implies s.push(x).index(i) != s.push(x).index(j) by {
            if j < s.len() {
                assert(s.push(x).index(i) == s.index(i));
                assert(s.push(x).index(j) == s.index(j));
                assert(s.index(i) != s.index(j)); // follows from precondition
            } else if j == s.len() { // new element x is at index s.len()
                assert(s.push(x).index(j) == x);
                assert(s.push(x).index(i) == s.index(i));
                assert(i < s.len());
                assert(!s.contains(x)); // follows from !b_contains_x
                assert(s.index(i) != x); // follows from s.index(i) != x and !s.contains(x) 
            }
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
// </vc-spec>
// <vc-code>
{
    let mut diff = Seq::<int>::empty();
    let mut i: int = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: int| diff.contains(x) <==> (exists|k: int| 0 <= k < i && a.index(k) == x && !b.contains(x)),
            forall|k: int, l: int| 0 <= k < l < diff.len() ==> diff.index(k) != diff.index(l)
    {
        let current_a_val = a.index(i);
        if !b.contains(current_a_val) {
            if !diff.contains(current_a_val) {
                let old_diff = diff.clone(); // Use clone for models
                diff = diff.push(current_a_val);
                proof {
                    uniqueness_preservation(old_diff, current_a_val, old_diff.contains(current_a_val));
                }
            }
        }
        i = i + 1;
    }

    // This assert is no longer needed as the invariant already proves the first postcondition
    // assert forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)) by {
    //     if diff.contains(x) {
    //         let idx = diff.index_of(x);
    //          assert(idx.is_Some());
    //         let some_idx = idx.unwrap();
    //         assert(0 <= some_idx < diff.len());
    //         assert(diff.index(some_idx) == x);
    //         // From invariant, `diff.contains(x)` implies `exists |k: int| 0 <= k < i && a.index(k) == x && !b.contains(x)`
    //         // which implies `a.contains(x)` and `!b.contains(x)`.
    //     } else {
    //         // If x is not in diff, then it means either x is not in a, or x is in b.
    //         // This is derived from the invariant:
    //         // `!(exists|k: int| 0 <= k < i && a.index(k) == x && !b.contains(x))`
    //         // which simplifies to `forall|k: int| !(0 <= k < i && a.index(k) == x) || b.contains(x)`.
    //         // If `a.contains(x)` and `!b.contains(x)`, then by definition of `diff` (what it accumulates),
    //         // it *must* have been added. So if it's not in `diff`, then either `!a.contains(x)` or `b.contains(x)`.
    //     }
    // };
    
    diff
}
// </vc-code>

fn main() {}

}