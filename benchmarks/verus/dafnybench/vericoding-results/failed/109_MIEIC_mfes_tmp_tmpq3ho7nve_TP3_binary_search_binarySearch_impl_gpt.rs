use vstd::prelude::*;

verus! {

// Checks if array 'a' is sorted.
spec fn is_sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found.

// Simple test cases to check the post-condition.

/*
a) Identify adequate pre and post-conditions for this method, 
and encode them as "requires" and "ensures" clauses in Verus. 
You can use the predicate below if needed.

b) Identify an adequate loop variant and loop invariant, and encode them 
as "decreases" and "invariant" clauses in Verus.
*/

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[i32], x: i32) -> (index: i32)
    requires is_sorted(a)
    ensures -1 <= index < a.len() && 
            (index != -1 ==> a[index as int] == x) &&
            (index == -1 ==> !a@.contains(x))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            forall|j: int| 0 <= j < i as int ==> a@[j] != x,
        decreases (a.len() - i) as int
    {
        let iprev = i;
        if a[i] == x {
            assert(0 <= i as int && i as int < a.len() as int);
            return i as i32;
        } else {
            i = i + 1;
            assert(i as int == iprev as int + 1);
            assert_forall_by(|j: int| {
                requires(0 <= j && j < i as int);
                ensures(a@[j] != x);
                if j < iprev as int {
                    // Holds from the previous invariant
                } else {
                    assert(iprev as int <= j);
                    assert(j < iprev as int + 1);
                    assert(j <= iprev as int);
                    assert(j == iprev as int);
                    assert(0 <= iprev as int && iprev as int < a.len() as int);
                    assert(a@[iprev as int] == a[iprev]);
                    assert(a[iprev] != x);
                }
            });
        }
    }
    assert(i as int == a.len() as int);
    assert_forall_by(|j: int| {
        requires(0 <= j && j < a.len() as int);
        ensures(a@[j] != x);
        assert(i as int == a.len() as int);
        assert(0 <= j && j < i as int);
    });
    assert(!exists|j: int| 0 <= j < a.len() as int && #[trigger] a@[j] == x);
    assert(!a@.contains(x));
    -1
}
// </vc-code>

fn main() {
}

}