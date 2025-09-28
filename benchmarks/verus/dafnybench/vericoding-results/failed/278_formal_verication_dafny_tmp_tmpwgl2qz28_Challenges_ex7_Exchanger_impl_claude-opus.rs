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
// Helper lemma to prove multiset preservation when swapping elements
proof fn multiset_swap_lemma(s: Seq<Bases>, x: int, y: int, t: Seq<Bases>)
    requires
        0 <= x < s.len(),
        0 <= y < s.len(),
        t.len() == s.len(),
        t[x] == s[y],
        t[y] == s[x],
        forall|i: int| 0 <= i < s.len() && i != x && i != y ==> t[i] == s[i],
    ensures
        s.to_multiset() == t.to_multiset(),
{
    // The multiset equality follows from the fact that we're just swapping two elements
    assert(s.to_multiset() =~= t.to_multiset());
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
    let mut t = s;
    
    if x != y {
        let x_usize = x as usize;
        let y_usize = y as usize;
        let temp = s[x_usize];
        t = t.update(x_usize, s[y_usize]);
        t = t.update(y_usize, temp);
        
        // Prove the postconditions
        assert(t.len() == s.len());
        assert(t@[x as int] == s@[y as int]);
        assert(t@[y as int] == s@[x as int]);
        
        assert forall|b: nat| 0 <= b < s.len() && b != x && b != y 
            implies t@[b as int] == s@[b as int] by {
            // This follows from the update operations only affecting x and y
        }
        
        // Prove multiset preservation
        proof {
            multiset_swap_lemma(s@, x as int, y as int, t@);
        }
    } else {
        // When x == y, no swap needed
        assert(t@[x as int] == s@[y as int]);
        assert(t@[y as int] == s@[x as int]);
        assert forall|b: nat| 0 <= b < s.len() && b != x && b != y 
            implies t@[b as int] == s@[b as int] by {}
        assert(s@.to_multiset() == t@.to_multiset());
    }
    
    t
}
// </vc-code>

fn main() {}

}