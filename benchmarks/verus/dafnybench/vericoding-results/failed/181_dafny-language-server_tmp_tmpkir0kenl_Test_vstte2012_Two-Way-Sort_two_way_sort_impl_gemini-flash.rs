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
fn sorted_pred(a: Seq<bool>) -> bool {
    forall|m: int, n: int| 0 <= m < n < a.len() ==> (!a[m] || a[n])
}

proof fn swap_multisets_lemma<T>(a: Seq<T>, i: int, j: int)
    requires
        0 <= i < j < a.len(),
    ensures
        ({
            let mut a_copy = a.to_vec();
            a_copy.swap(i as usize, j as usize);
            multisets(a_copy@) == multisets(a)
        }),
{
    assert(multisets(a) == multisets(a.take(i))
        .add(Multiset::singleton(a[i]))
        .add(multisets(a.subrange(i + 1, j)))
        .add(Multiset::singleton(a[j]))
        .add(multisets(a.skip(j + 1)))) by {
        multisets_axiom(a);
    };

    let mut b = a.to_vec();
    b.swap(i as usize, j as usize);
    let b_seq = b@;

    assert(b_seq.take(i) == a.take(i)) by { };
    assert(b_seq.skip(j + 1) == a.skip(j + 1)) by { };
    assert(b_seq.subrange(i + 1, j) == a.subrange(i + 1, j)) by { };

    assert(b_seq[i] == a[j]);
    assert(b_seq[j] == a[i]);

    assert(multisets(b_seq) == multisets(b_seq.take(i))
        .add(Multiset::singleton(b_seq[i]))
        .add(multisets(b_seq.subrange(i + 1, j)))
        .add(Multiset::singleton(b_seq[j]))
        .add(multisets(b_seq.skip(j + 1)))) by {
        multisets_axiom(b_seq);
    };

    assert(multisets(b_seq) == multisets(a.take(i))
        .add(Multiset::singleton(a[j]))
        .add(multisets(a.subrange(i + 1, j)))
        .add(Multiset::singleton(a[i]))
        .add(multisets(a.skip(j + 1)))) by {
        assert(multisets(b_seq.take(i)) == multisets(a.take(i)));
        assert(multisets(b_seq.subrange(i + 1, j)) == multisets(a.subrange(i + 1, j)));
        assert(multisets(b_seq.skip(j + 1)) == multisets(a.skip(j + 1)));
        assert(b_seq[i] == a[j]);
        assert(b_seq[j] == a[i]);
    };

    Multiset::add_commutative_associative(Multiset::singleton(a[j]), multisets(a.subrange(i + 1, j)), Multiset::singleton(a[i]));
    Multiset::add_commutative_associative(Multiset::singleton(a[j]).add(multisets(a.subrange(i + 1, j))), Multiset::singleton(a[i]), Multiset::empty());

    assert(multisets(a.take(i))
        .add(Multiset::singleton(a[j]))
        .add(multisets(a.subrange(i + 1, j)))
        .add(Multiset::singleton(a[i]))
        .add(multisets(a.skip(j + 1)))
        ==
        multisets(a.take(i))
        .add(Multiset::singleton(a[i]))
        .add(multisets(a.subrange(i + 1, j)))
        .add(Multiset::singleton(a[j]))
        .add(multisets(a.skip(j + 1)))) by {
        Multiset::add_commutative_associative(Multiset::singleton(a[j]), multisets(a.subrange(i + 1, j)), Multiset::singleton(a[i]));
        Multiset::add_commutative_associative(multisets(a.take(i)), Multiset::singleton(a[j]).add(multisets(a.subrange(i + 1, j))), Multiset::singleton(a[i]).add(multisets(a.skip(j + 1))));
        assert(multisets(a.take(i)).add(Multiset::singleton(a[j])).add(multisets(a.subrange(i + 1, j))).add(Multiset::singleton(a[i])).add(multisets(a.skip(j + 1))) ==
            multisets(a.take(i)).add(Multiset::singleton(a[i])).add(Multiset::singleton(a[j])).add(multisets(a.subrange(i + 1, j))).add(multisets(a.skip(j + 1))));
    };
    assert(multisets(b_seq) == multisets(a));
}

proof fn swap_preserves_other_elements<T>(a: Seq<T>, i: int, j: int)
    requires
        0 <= i < j < a.len(),
    ensures
        forall|m: int| 0 <= m < a.len() && m != i && m != j ==> {
            let mut a_copy = a.to_vec();
            a_copy.swap(i as usize, j as usize);
            a_copy@[m] == a@[m]
        },
{
    let mut b: Vec<T> = a.to_vec();
    b.swap(i as usize, j as usize);
    let b_seq = b@;

    assert forall|m: int| 0 <= m < a.len() && m != i && m != j implies b_seq[m] == a[m] by {
        if m < i {
            assert(b_seq.take(i) == a.take(i));
            assert(b_seq[m] == a[m]);
        } else if m > j {
            assert(b_seq.skip(j + 1) == a.skip(j + 1));
            assert(b_seq[m] == a[m]);
        } else { // i < m < j
            assert(b_seq.subrange(i + 1, j) == a.subrange(i + 1, j));
            assert(b_seq[m] == a[m]);
        }
    }
}

proof fn swap_elements_are_swapped<T>(a: Seq<T>, i: int, j: int)
    requires
        0 <= i < j < a.len(),
    ensures
        ({
            let mut a_copy = a.to_vec();
            a_copy.swap(i as usize, j as usize);
            a_copy@[i] == a@[j] && a_copy@[j] == a@[i]
        }),
{
    let mut b: Vec<T> = a.to_vec();
    b.swap(i as usize, j as usize);
    let b_seq = b@;
    assert(b_seq[i] == a[j]);
    assert(b_seq[j] == a[i]);
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

    while i < j
        invariant
            i as int <= j as int + 1,
            0 <= i as int,
            a.len() == 0 || j as int < a.len() as int,
            forall|k: int| 0 <= k < i as int ==> !a[k],
            forall|k: int| j as int < k < a.len() ==> a[k],
            multisets(a@) == multisets(old(a)@),
    {
        if a[i] {
            if !a[j] {
                // Pre-state assertion for ghost code
                let pre_a_seq = a@;
                proof {
                    swap_multisets_lemma(pre_a_seq, i as int, j as int);
                    swap_preserves_other_elements(pre_a_seq, i as int, j as int);
                    swap_elements_are_swapped(pre_a_seq, i as int, j as int);
                }
                a.swap(i, j);
                proof {
                    let post_a_seq = a@;
                    // Proving forall|k: int| 0 <= k < i as int ==> !post_a_seq[k]
                    assert forall|k: int| 0 <= k < i as int implies !post_a_seq[k] by {
                        assert(post_a_seq[k] == pre_a_seq[k]); // Because k < i, and i < j, so k is not i or j
                        assert(!pre_a_seq[k]); // From loop invariant before swap
                    }
                    // Proving forall|k: int| j_old as int < k < a.len() ==> post_a_seq[k]
                    let j_old = j;
                    assert forall|k: int| j_old as int < k < a.len() implies post_a_seq[k] by {
                        assert(post_a_seq[k] == pre_a_seq[k]); // Because k > j_old, and i < j_old, so k is not i or j_old
                        assert(pre_a_seq[k]); // From loop invariant before swap
                    }
                }
            }
            j = j - 1;
        } else {
            i = i + 1;
        }
    }
    proof {
        assert(i as int >= j as int);

        assert forall|m: int, n: int| 0 <= m < n < a.len() implies (!a[m] || a[n]) by {
            if n < i as int { // both are in the 'false' region
                assert(!a[m]); // from loop invariant (k < i)
            } else if m > j as int { // both are in the 'true' region
                assert(a[n]); // from loop invariant (k > j)
            } else if m < i as int && n > j as int { // m is 'false' and n is 'true'
                assert(!a[m]); // from loop invariant (k < i)
                assert(a[n]); // from loop invariant (k > j)
            } else if m < i as int && i as int <= n && n <= j as int { // m is 'false', n is in the 'middle' region
                assert(!a[m]); // from loop invariant (k < i)
                // If the loop terminated, it means either i == j or i == j + 1.
                // If i == j, n can be i.
                // If i == j + 1, the middle region is empty.
                // This case is impossible because if n is in the middle region and m < i, then i must be <= n.
                // But i > j at termination, so if n <= j, then n < i must hold, which contradicts n >= i.
            } else if i as int <= m && m <= j as int && n > j as int { // m is in the 'middle' region, n is 'true'
                assert(a[n]); // from loop invariant (k > j)
                // Similar to the above, this case is impossible at termination.
            } else { // i <= m < n <= j, both in the 'middle' region (which at termination means i == m == n == j, single element)
                // This means i == j and m=i, n=i, which contradicts m < n.
                // Or if i and j crossed, the region [i .. j] is empty.
                // Example: a.len() = 0 -> i=0, j=18446744073709551615 ; loop condition i<j fails immediately.
                // Example: a = [true, false]. i=0, j=1.  a[0] is true, !a[1] is true. Swap. a = [false, true]. i=0, j=1.
                // Next iter: i=0, j=0. Loop terminates.
                // i = 0, j = 0.
                // !a[k] for k < 0, a[k] for k > 0.
                // So now we have to prove !a[0] || a[1].
                // The crucial part is that i, j have crossed, meaning all elements up to j have been processed to be false if they belong on the left,
                // and all elements from i have been processed to be true if they belong on the right.
                // The invariant states: all values checked to the left of i are false, and all values checked to the right of j are true.
                // When i >= j, the entire array is covered by these two properties.
                // if n < i, then !a[n]. Thus !a[m] || !a[n] -> !a[m].  (If m < n, then m < i too).
                assert(!a[m] && !a[n] || a[m] && a[n] || !a[m] && a[n]); // General cases.
                if !(m < i as int) && !(n > j as int) {
                    // This implies i <= m < n <= j.
                    // But at termination, i >= j.
                    // The only possibility for i <= m < n <= j with i >= j is if the range is empty.
                    // Which means this `if` block is unreachable at termination.
                }

                // If i == a.len() and j == usize::MAX (or equivalent, when a.len() == 0)
                // The loop invariant states sufficient properties for sorted_pred.
                // This must hold at termination:
                // forall k' in [0..i), a[k'] == false
                // forall k'' in (j..a.len()), a[k''] == true

                // Since i >= j:
                // Case 1: i = j (e.g., [false, true]) -> i=1,j=0. The middle range [i..j] is empty
                // Case 2: i = j+1 (e.g. initial empty array) -> i=0,j=18446... The middle range is empty
            }
        }
        assert(sorted_pred(a@));
    }
}
// </vc-code>

fn main() {}

}