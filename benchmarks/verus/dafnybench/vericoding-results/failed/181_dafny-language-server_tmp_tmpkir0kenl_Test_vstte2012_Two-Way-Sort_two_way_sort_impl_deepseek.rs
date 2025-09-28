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
spec fn count_false(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        if !s[0] {
            count_false(s.subrange(1, s.len() as int)) + 1
        } else {
            count_false(s.subrange(1, s.len() as int))
        }
    }
}

proof fn multisets_singleton_bool(b: bool)
    ensures
        multisets(Seq::<bool>::singleton(b)) == Multiset::singleton(b),
{}

proof fn multisets_cons_bool(b: bool, s: Seq<bool>)
    ensures
        multisets(s.cons(b)) == Multiset::singleton(b).add(multisets(s)),
{}

proof fn count_false_multisets_relation(s: Seq<bool>)
    ensures
        multisets(s) == Multiset::empty().add_n(count_false(s), false).add_n(s.len() as nat - count_false(s), true),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(multisets(Seq::empty()) == Multiset::empty());
        assert(count_false(Seq::empty()) == 0);
    } else {
        count_false_multisets_relation(s.subrange(1, s.len() as int));
        multisets_cons_bool(s[0], s.subrange(1, s.len() as int));
        assert(s.cons(s[0]) == s);
    }
}

proof fn permutation_swap<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j,
    ensures
        multisets(s.update(i, s[j]).update(j, s[i])) == multisets(s),
{}

proof fn count_false_subrange(s: Seq<bool>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        count_false(s.subrange(start, end)) == count_false(s) - count_false(s.subrange(0, start)) - count_false(s.subrange(end, s.len())),
    decreases end - start,
{
    if start == end {
        assert(s.subrange(start, end) == Seq::empty());
        assert(count_false(Seq::empty()) == 0);
    } else {
        count_false_subrange(s, start + 1, end);
        if !s[start] {
            assert(count_false(s.subrange(start, end)) == count_false(s.subrange(start + 1, end)) + 1);
        } else {
            assert(count_false(s.subrange(start, end)) == count_false(s.subrange(start + 1, end)));
        }
    }
}

proof fn swap_preserves_multiset<T>(a: Seq<T>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        multisets(a.update(i, a[j]).update(j, a[i])) == multisets(a),
{
    permutation_swap(a, i, j);
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
    let mut j: usize = a.len() - 1;
    
    while i <= j {
        invariant
            0 <= i,
            j < a@.len(),
            i <= j + 1,
            forall|m: int| 0 <= m < i ==> !a@[m],
            forall|m: int| j < m < a@.len() ==> a@[m],
            i + (a@.len() - j - 1) == count_false(old(a)@),
            multisets(a@) == multisets(old(a)@),
        {
            if a[i] {
                proof {
                    swap_preserves_multiset(a@, i as int, j as int);
                }
                swap(a, i, j);
                j = j - 1;
            } else {
                i = i + 1;
            }
        }
        
        proof {
            assert(a@.len() == old(a)@.len());
            count_false_multisets_relation(old(a)@);
            count_false_multisets_relation(a@);
        }
    }
}
// </vc-code>

fn main() {}

}