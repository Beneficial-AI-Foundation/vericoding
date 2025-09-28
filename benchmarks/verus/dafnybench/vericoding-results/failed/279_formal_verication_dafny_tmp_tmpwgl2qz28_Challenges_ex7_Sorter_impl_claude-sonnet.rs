use vstd::prelude::*;

verus! {

// see pdf 'ex6 & 7 documentation' for excercise question


#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum Bases {
    A,
    C,
    G,
    T,
}

//swaps two sequence indexes
fn exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 
        0 < s.len() && x < s.len() && y < s.len()
    ensures 
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b],
        t[x as int] == s[y as int] && s[x as int] == t[y as int],
        s.to_multiset() == t.to_multiset()
{
    assume(false);
    s
}

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
// Helper lemma to prove that below defines a total order
proof fn lemma_below_total_order(x: Bases, y: Bases)
    ensures below(x, y) || below(y, x)
{
}

// Helper lemma for transitivity of below
proof fn lemma_below_transitive(x: Bases, y: Bases, z: Bases)
    requires below(x, y) && below(y, z)
    ensures below(x, z)
{
}

// Helper to convert Bases to ordering value
spec fn base_to_int(b: Bases) -> int {
    match b {
        Bases::A => 0,
        Bases::C => 1, 
        Bases::G => 2,
        Bases::T => 3,
    }
}

// Lemma connecting below with integer ordering
proof fn lemma_below_iff_int_order(x: Bases, y: Bases)
    ensures below(x, y) <==> base_to_int(x) <= base_to_int(y)
{
}

// Implementation of exchanger function
fn exchanger_impl(s: Seq<Bases>, x: usize, y: usize) -> (t: Seq<Bases>)
    requires 
        0 < s.len() && x < s.len() && y < s.len()
    ensures 
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> #[trigger] t[b] == s[b],
        t[x as int] == s[y as int] && s[x as int] == t[y as int],
        s.to_multiset() == t.to_multiset()
{
    s.update(x as int, s@[y]).update(y as int, s@[x])
}

// Insertion sort implementation
fn insertion_sort(s: Seq<Bases>) -> (result: Seq<Bases>)
    requires 0 < s.len()
    ensures 
        result.len() == s.len(),
        bordered(result),
        s.to_multiset() == result.to_multiset()
{
    let mut result = s;
    let mut i: usize = 1;
    
    while i < result.len()
        invariant
            0 < i <= result.len(),
            result.len() == s.len(),
            s.to_multiset() == result.to_multiset(),
            forall|j: int, k: int| 0 <= j < k < i ==> below(result[j], result[k])
    {
        let mut j = i;
        while j > 0 && !below(result@[j-1], result@[j])
            invariant
                0 <= j <= i < result.len(),
                result.len() == s.len(),
                s.to_multiset() == result.to_multiset(),
                forall|a: int, b: int| 0 <= a < b < i && b != j ==> below(result[a], result[b]),
                forall|k: int| j < k <= i ==> below(result[j as int], result[k])
        {
            proof {
                lemma_below_iff_int_order(result@[j-1], result@[j]);
                lemma_below_iff_int_order(result@[j], result@[j-1]);
            }
            
            result = exchanger_impl(result, j-1, j);
            j = j - 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn sorter(bases: Seq<Bases>) -> (sobases: Seq<Bases>)
    requires 
        0 < bases.len()
    ensures 
        sobases.len() == bases.len(),
        bordered(sobases),
        bases.to_multiset() == sobases.to_multiset()
// </vc-spec>
// <vc-code>
{
    if bases.len() == 1 {
        return bases;
    }
    
    insertion_sort(bases)
}
// </vc-code>

fn main() {}

}