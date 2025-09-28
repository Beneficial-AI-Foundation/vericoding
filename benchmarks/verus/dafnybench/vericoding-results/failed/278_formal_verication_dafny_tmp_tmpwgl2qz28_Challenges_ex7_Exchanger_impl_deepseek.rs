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
spec fn swap(s: Seq<Bases>, x: nat, y: nat) -> Seq<Bases> {
    if x == y {
        s
    } else {
        s.update(x as int, s[y as int]).update(y as int, s[x as int])
    }
}

proof fn swap_swap_identity(s: Seq<Bases>, x: nat, y: nat)
    requires
        x < s.len(),
        y < s.len(),
    ensures
        swap(swap(s, x, y), x, y) == s,
{
    if x != y {
        assert(swap(s, x, y)[x as int] == s[y as int]);
        assert(swap(s, x, y)[y as int] == s[x as int]);
        assert(forall|b: nat| b < s.len() && b != x && b != y ==> swap(s, x, y)[b as int] == s[b as int]);
        
        let s2 = swap(s, x, y);
        assert(swap(s2, x, y)[x as int] == s2[y as int]);
        assert(swap(s2, x, y)[x as int] == s[x as int]);
        assert(swap(s2, x, y)[y as int] == s2[x as int]);
        assert(swap(s2, x, y)[y as int] == s[y as int]);
        assert(forall|b: nat| b < s2.len() && b != x && b != y ==> swap(s2, x, y)[b as int] == s2[b as int]);
        assert(forall|b: nat| b < s2.len() && b != x && b != y ==> swap(s2, x, y)[b as int] == s[b as int]);
    }
}

proof fn swap_preserves_multiset(s: Seq<Bases>, x: nat, y: nat)
    requires
        x < s.len(),
        y < s.len(),
    ensures
        swap(s, x, y).to_multiset() == s.to_multiset(),
{
    if x != y {
        vstd::multiset::Multiset::lemma_swap(s.to_multiset(), x as int, y as int);
    }
}

proof fn seq_clone_spec<A>(s: Seq<A>) 
    ensures 
        s.clone() == s
{}

proof fn swap_equals_set_operations(s: Seq<Bases>, x: nat, y: nat)
    requires
        x < s.len(),
        y < s.len(),
    ensures
        swap(s, x, y) == s.set(x as int, s[y as int]).set(y as int, s[x as int]),
{
    if x != y {
        assert(swap(s, x, y)[x as int] == s[y as int]);
        assert(swap(s, x, y)[y as int] == s[x as int]);
        assert(forall|b: nat| b < s.len() && b != x && b != y ==> swap(s, x, y)[b as int] == s[b as int]);
    }
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
    proof { seq_clone_spec(s); }
    let mut t = s;
    proof {
        swap_preserves_multiset(s, x, y);
    }
    assert(s.to_multiset() === t.to_multiset());
    proof { swap_equals_set_operations(s, x, y); }
    let x_usize: usize = x as usize;
    let y_usize: usize = y as usize;
    let tmp = t[x_usize];
    t = t.set(x_usize, t[y_usize]);
    t = t.set(y_usize, tmp);
    proof {
        assert(t[x as int] == s[y as int]);
        assert(t[y as int] == s[x as int]);
        assert(forall|b: nat| b < s.len() && b != x && b != y ==> t[b as int] == s[b as int]) by {
            assert(forall|b: nat| b < s.len() && b != x && b != y ==> #[trigger] t[b as int] == s[b as int]);
        }
        assert(t.to_multiset() == s.to_multiset()) by {
            assert(t === swap(s, x, y));
        }
    }
    t
}
// </vc-code>

fn main() {}

}