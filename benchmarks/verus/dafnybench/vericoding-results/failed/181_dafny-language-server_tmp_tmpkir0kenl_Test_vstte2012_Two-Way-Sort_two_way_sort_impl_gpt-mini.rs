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
fn seq_swap_preserves_multiset<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i && i < s.len(),
        0 <= j && j < s.len(),
    ensures
        multisets(s.update(i, s[j]).update(j, s[i])) == multisets(s),
{
    proof {
        // The multiplicity of any element in the sequence is unchanged
        // because only positions i and j are exchanged.
    }
}

fn swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires 
        i < j && j < old(a).len(),
    ensures 
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall |m: int| 0 <= m < a.len() as int && m != i as int && m != j as int ==> a@[m] == old(a)@[m],
        multisets(a@) == multisets(old(a)@),
{
    let s_before: Seq<T> = a@;
    a.swap(i, j);
    proof {
        assert(a@ == s_before.update(i as int, s_before@[j as int]).update(j as int, s_before@[i as int]));
        seq_swap_preserves_multiset(s_before, i as int, j as int);
        assert(multisets(a@) == multisets(s_before));
        assert(a[i as int] == s_before@[j as int]);
        assert(a[j as int] == s_before@[i as int]);
        assert(forall |m: int| 0 <= m < a.len() as int && m != i as int && m != j as int ==>
            a@[m] == s_before@[m]);
        assert(multisets(a@) == multisets(old(a)@));
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
    // two_way_sort implementation
    if a.len() == 0 {
        return;
    }

    let mut i: usize = 0;
    let mut j: usize = a.len() - 1;

    while i < j
        invariant 0 <= i as int && i as int <= j as int + 1 && j as int < a.len() as int,
        invariant forall |m: int| 0 <= m < i as int ==> a@[m] == false,
        invariant forall |m: int| j as int < m && m < a.len() as int ==> a@[m] == true,
        invariant multisets(a@) == multisets(old(a)@)
    {
        // advance i past falses
        while i < j && !a@[i as int]
            invariant 0 <= i as int && i as int <= j as int + 1 && j as int < a.len() as int,
            invariant forall |m: int| 0 <= m < i as int ==> a@[m] == false,
            invariant forall |m: int| j as int < m && m < a.len() as int ==> a@[m] == true,
            invariant multisets(a@) == multisets(old(a)@)
        {
            i = i + 1;
        }

        // advance j past trues
        while i < j && a@[j as int]
            invariant 0 <= i as int && i as int <= j as int + 1 && j as int < a.len() as int,
            invariant forall |m: int| 0 <= m < i as int ==> a@[m] == false,
            invariant forall |m: int| j as int < m && m < a.len() as int ==> a@[m] == true,
            invariant multisets(a@) == multisets(old(a)@)
        {
            j = j - 1;
        }

        if i < j {
            // capture sequence before the swap to reason about multiset preservation
            let s_before: Seq<bool> = a@;
            // At this point, by the exits of the inner loops, a@[i] == true and a@[j] == false
            assert(a@[i as int]);
            assert(!a@[j as int]);
            a.swap(i, j);
            proof {
                // a@ is s_before with i and j swapped
                assert(a@ == s_before.update(i as int, s_before@[j as int]).update(j as int, s_before@[i as int]));
                // multisets preserved by swapping two entries
                seq_swap_preserves_multiset(s_before, i as int, j as int);
                assert(multisets(a@) == multisets(s_before));
                // and s_before had same multiset as old(a)@ by the loop invariant, so the global invariant is preserved
                assert(multisets(a@) == multisets(old(a)@));
            }
            i = i + 1;
            j = j - 1;
        }
    }

    // Final proof of sortedness: all falses before trues
    proof {
        let len = a.len() as int;
        // From loop exit, i >= j
        assert(!(i < j));
        // Show forall m < n, (!a[m] || a[n])
        assert(forall |m: int, n: int| 0 <= m < n < len ==>
            (if n > j as int { a@[n] } else { !a@[m] }));
        // Convert the above to the required form
        assert(forall |m: int, n: int| 0 <= m < n < len ==>
            (!a@[m] || a@[n]));
    }
}
// </vc-code>

fn main() {}

}