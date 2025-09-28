use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

// This method is a slight generalization of the
// code provided in the problem statement since it
// is generic in the type of the array elements.

spec fn multisets<T>(s: Seq<T>) -> Multiset<T>
    decreases s.len(),
{
    if s.len() == 0 { 
        Multiset::empty() 
    } else { 
        Multiset::singleton(s[0]).add(multisets(s.subrange(1, s.len() as int)))
    }
}

fn swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires 
        i < j < old(a).len(),
    ensures 
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|m: int| 0 <= m < a.len() && m != i && m != j ==> a[m] == old(a)[m],
        multisets(a@) == multisets(old(a)@),
{
    assume(false);
}

// This method is a direct translation of the pseudo
// code given in the problem statement.
// The first postcondition expresses that the resulting
// array is sorted, that is, all occurrences of "false"
// come before all occurrences of "true".
// The second postcondition expresses that the post-state
// array is a permutation of the pre-state array. To express
// this, we use Verus's built-in multisets. The built-in
// function "multisets" takes a sequence and yields the
// multiset of the sequence elements.
// Note that Verus guesses a suitable ranking function
// for the termination proof of the while loop.
// We use the loop guard from the given pseudo-code.  However,
// the program also verifies with the stronger guard "i < j"
// (without changing any of the other specifications or
// annotations).

// <vc-helpers>
// Helper lemma to show that multisets are preserved through swaps
proof fn multisets_swap_lemma<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < j < s.len(),
    ensures
        multisets(s) == multisets(s.update(i, s[j]).update(j, s[i])),
    decreases s.len(),
{
    let s_swapped = s.update(i, s[j]).update(j, s[i]);
    
    // We need to show that the multisets are equal
    // This follows by induction on the sequence length
    if s.len() == 0 {
        // Base case: empty sequence (contradiction with precondition)
        assert(false);
    } else if s.len() == 1 {
        // Single element (contradiction since i < j)
        assert(false);
    } else {
        // The multiset is preserved because we're just rearranging elements
        // The actual elements remain the same, just positions change
        assert(multisets(s) =~= multisets(s_swapped));
    }
}
// </vc-helpers>

// <vc-spec>
fn two_way_sort(a: &mut Vec<bool>)
    ensures 
        forall|m: int, n: int| 0 <= m < n < a.len() ==> (!a[m] || a[n]),
        multisets(a@) == multisets(old(a)@),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = if a.len() > 0 { (a.len() - 1) as usize } else { 0 };
    
    while i <= j
        invariant
            j < a.len(),
            i <= a.len(),
            multisets(a@) == multisets(old(a)@),
            forall|m: int| 0 <= m < i ==> !a[m],
            forall|n: int| j < n < a.len() ==> a[n],
        decreases j - i,
    {
        if !a[i] {
            i = i + 1;
        } else if a[j] {
            if j > 0 {
                j = j - 1;
            } else {
                // j == 0 and a[j] is true, i must also be 0
                // Since a[0] is true and we're done
                break;
            }
        } else {
            // a[i] is true and a[j] is false, so swap them
            assert(i < j);  // This must hold since a[i] != a[j]
            swap(a, i, j);
            i = i + 1;
            if j > 0 {
                j = j - 1;
            } else {
                break;
            }
        }
    }
    
    // After the loop, prove the postcondition
    assert forall|m: int, n: int| 0 <= m < n < a.len() implies (!a[m] || a[n]) by {
        if m < i {
            assert(!a[m]);
        }
        if n > j {
            assert(a[n]);
        }
        if i > j {
            // The regions have met or crossed
            if m < i && n > j {
                assert(!a[m]);
                assert(a[n]);
            }
        } else if i == j {
            // Single element in the middle
            if m < i {
                assert(!a[m]);
            } else if n > j {
                assert(a[n]);
            } else if m == i && n == j {
                assert(m == n);  // Contradiction with m < n
            }
        }
    }
}
// </vc-code>

fn main() {}

}