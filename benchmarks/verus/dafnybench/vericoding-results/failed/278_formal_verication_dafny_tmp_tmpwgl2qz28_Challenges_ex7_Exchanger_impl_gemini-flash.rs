use vstd::prelude::*;

verus! {

// see pdf 'ex6 & 7 documentation' for excercise question

#[derive(PartialEq, Eq, Clone, Copy)]
enum Bases {
    A,
    C,
    G,
    T,
}

//swaps two sequence indexes

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
spec fn below(first: Bases, second: Bases) -> bool {
    first == second ||
    first == Bases::A || 
    (first == Bases::C && (second == Bases::G || second == Bases::T)) || 
    (first == Bases::G && second == Bases::T) ||
    second == Bases::T
}

//checks if a sequence is in base order
spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s[j], s[k])
}

// <vc-helpers>
fn swap_bases(s: &mut Vec<Bases>, x: int, y: int)
    requires
        0 <= x < s.len(),
        0 <= y < s.len(),
    ensures
        s.len() == old(s).len(),
        s[x] == old(s)[y],
        s[y] == old(s)[x],
        forall |i: int| 0 <= i < s.len() && i != x && i != y ==> s[i] == old(s)[i],
{
    let temp = s[x];
    s[x] = s[y];
    s[y] = temp;
}
// </vc-helpers>

// <vc-spec>
fn exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 
        0 < s.len(),
        x < s.len(),
        y < s.len(),
    ensures 
        t.len() == s.len(),
        forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> t[b as int] == s[b as int],
        t[x as int] == s[y as int] && s[x as int] == t[y as int],
        s.to_multiset() == t.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mut t = s.to_vec();
    proof {
        assert(t.len() == s.len());
        assert(t.to_multiset() == s.to_multiset()); // This holds because t is initialized from s
        assert(s[x as int] == t[x as int]);
        assert(s[y as int] == t[y as int]);
    }

    let old_s_vec = t.clone(); // Capture the state of t before swap, which is old(s)

    swap_bases(&mut t, x as int, y as int);

    proof {
        assert(t.len() == s.len());
        assert(t[x as int] == old_s_vec[y as int]); // Because old_s_vec was 't' before swap
        assert(t[y as int] == old_s_vec[x as int]);
        assert(t[x as int] == s[y as int]); // Since old_s_vec was s.to_vec()
        assert(t[y as int] == s[x as int]); // Since old_s_vec was s.to_vec()

        forall |b: nat| 0 <= b < s.len() && (b as int) != x as int && (b as int) != y as int implies t[b as int] == s[b as int] by {
            assert(t[b as int] == old_s_vec[b as int]); // From postcondition of swap_bases
            assert(old_s_vec[b as int] == s[b as int]); // From initialization of old_s_vec from s
        }

        let s_multiset_temp = s.to_multiset();
        let t_multiset_temp = t.to_multiset();
        
        assert forall |elem: Bases| #[trigger] s_multiset_temp.count(elem) == t_multiset_temp.count(elem) by {
            let old_x_val = s[x as int];
            let old_y_val = s[y as int];

            // Consider the multiset counts.
            // The elements involved in the swap are s[x] and s[y].
            // After swap, t[x] = s[y] and t[y] = s[x].
            // All other elements are unchanged.

            // To show s.to_multiset() == t.to_multiset(), we need to show that the count of each element is the same.
            // Let's consider an arbitrary element 'elem' of type Bases.
            //
            // Case 1: elem is s[x] (the original value at index x)
            //   - If x and y are the same index, no effective swap happens. The multisets are obviously equal.
            //   - If x and y are different indices:
            //     - The count of s[x] in 's' is its original count.
            //     - In 't', the element originally at 'x' is now at 'y'. The element originally at 'y' is now at 'x'.
            //     - If s[x] == s[y], then the elements at x and y are simply swapped, but their values are the same.
            //       The count of s[x] doesn't change because s[x] (which is also s[y]) is still present at both x and y.
            //     - If s[x] != s[y]:
            //       The element s[x] moves from index x to index y.
            //       The element s[y] moves from index y to index x.
            //       All other elements remain in their positions.
            //       The total count of s[x] and s[y] in the multiset remains the same, because they just changed positions internally.
            
            // This is a more general proof for multiset equality after a swap of two elements.
            // The number of occurrences of an element 'k' in `s` is:
            // count(k, s) = (if k == s[x] then 1 else 0) + (if k == s[y] then 1 else 0) + sum_{i != x, y} (if k == s[i] then 1 else 0)
            // The number of occurrences of an element 'k' in `t` is:
            // count(k, t) = (if k == t[x] then 1 else 0) + (if k == t[y] then 1 else 0) + sum_{i != x, y} (if k == t[i] then 1 else 0)
            // We know t[x] == s[y] and t[y] == s[x], and t[i] == s[i] for i != x, y.
            // So, for i != x, y, (if k == t[i] then 1 else 0) == (if k == s[i] then 1 else 0).
            // Thus, we only need to show:
            // (if k == s[x] then 1 else 0) + (if k == s[y] then 1 else 0) == (if k == t[x] then 1 else 0) + (if k == t[y] then 1 else 0)
            // That is, (if k == s[x] then 1 else 0) + (if k == s[y] then 1 else 0) == (if k == s[y] then 1 else 0) + (if k == s[x] then 1 else 0).
            // This is clearly true. Therefore, the counts are equal for any 'elem'.

            // Verus doesn't need a specific breakdown by cases if the base logic is covered by multiset properties.
            // However, to satisfy the verifier, we can explicitly show the values.

            assert(t.to_seq().count(elem) == old_s_vec.to_seq().count(elem)); // This comes from the postcondition of swap_bases on counts for the underlying sequence.
            assert(s.to_multiset().count(elem) == t.to_multiset().count(elem));
        }
        assert(s.to_multiset() == t.to_multiset());
    }
    t.to_seq()
}
// </vc-code>

fn main() {}

}