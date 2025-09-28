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
spec fn swap_seq<T>(s: Seq<T>, i: nat, j: nat) -> Seq<T>
    recommends
        i < s.len(),
        j < s.len(),
{
    s.update(i as int, s[j as int]).update(j as int, s[i as int])
}

fn exec_swap_seq<T: Copy>(s: Seq<T>, i: usize, j: usize) -> (result: Seq<T>)
    requires
        i < s.len(),
        j < s.len(),
    ensures
        result == swap_seq(s, i as nat, j as nat),
{
    let temp = s[j as int];
    let s1 = s.update(i as int, temp);
    let result = s1.update(j as int, s[i as int]);
    
    proof {
        assert(result == s.update(i as int, s[j as int]).update(j as int, s[i as int]));
    }
    
    result
}

proof fn swap_seq_len<T>(s: Seq<T>, i: nat, j: nat)
    requires
        i < s.len(),
        j < s.len(),
    ensures
        swap_seq(s, i, j).len() == s.len(),
{
}

proof fn swap_seq_preserves_other_elements<T>(s: Seq<T>, i: nat, j: nat, k: nat)
    requires
        i < s.len(),
        j < s.len(),
        k < s.len(),
        k != i && k != j,
    ensures
        swap_seq(s, i, j)[k as int] == s[k as int],
{
}

proof fn swap_seq_swaps_elements<T>(s: Seq<T>, i: nat, j: nat)
    requires
        i < s.len(),
        j < s.len(),
    ensures
        swap_seq(s, i, j)[i as int] == s[j as int],
        swap_seq(s, i, j)[j as int] == s[i as int],
{
}

proof fn swap_seq_preserves_multiset<T>(s: Seq<T>, i: nat, j: nat)
    requires
        i < s.len(),
        j < s.len(),
    ensures
        swap_seq(s, i, j).to_multiset() == s.to_multiset(),
{
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
    let result = exec_swap_seq(s, x as usize, y as usize);
    
    proof {
        swap_seq_len(s, x, y);
        swap_seq_swaps_elements(s, x, y);
        swap_seq_preserves_multiset(s, x, y);
        
        assert forall|b: nat| 0 <= b < s.len() && b != x && b != y implies result[b as int] == s[b as int] by {
            swap_seq_preserves_other_elements(s, x, y, b);
        };
    }
    
    result
}
// </vc-code>

fn main() {}

}