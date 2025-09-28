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
// Updated helper code and proofs to support sorter implementation

// Helper to count occurrences of a base in a sequence (proof-level)
proof fn count_occ(s: Seq<Bases>, b: Bases) -> nat {
    let mut acc: nat = 0;
    let mut i: int = 0;
    while i < s.len() {
        invariant 0 <= i && i <= s.len();
        invariant acc <= s.len() as nat;
        if s[i] == b {
            acc = acc + 1;
        }
        i = i + 1;
    }
    acc
}

// Proof that converting a Vec<Bases> to Seq<Bases> preserves length
proof fn vec_to_seq_len_preserved(v: &Vec<Bases>)
    ensures v.to_seq().len() == v.len()
{
    // by definition of to_seq
}

// Simple lemma: for any sequence s, sum of counts of all four Bases equals length
proof fn sum_counts_equals_len(s: Seq<Bases>)
    ensures count_occ(s, Bases::A) + count_occ(s, Bases::C) + count_occ(s, Bases::G) + count_occ(s, Bases::T) == s.len()
{
    // Prove by iterating through sequence and accumulating
    let mut a: nat = 0;
    let mut c: nat = 0;
    let mut g: nat = 0;
    let mut t: nat = 0;
    let mut i: int = 0;
    while i < s.len() {
        invariant
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
// Updated helper code and proofs to support sorter implementation

// Helper to count occurrences of a base in a sequence (proof-level)
proof fn count_occ(s: Seq<Bases>, b: Bases) -> nat {
    let mut acc: nat = 0;
    let mut i: int = 0;
    while i < s.len() {
        invariant 0 <= i && i <= s.len();
        invariant acc <= s.len() as nat;
        if s[i] == b {
            acc = acc + 1;
        }
        i = i + 1;
    }
    acc
}

// Proof that converting a Vec<Bases> to Seq<Bases> preserves length
proof fn vec_to_seq_len_preserved(v: &Vec<Bases>)
    ensures v.to_seq().len() == v.len()
{
    // by definition of to_seq
}

// Simple lemma: for any sequence s, sum of counts of all four Bases equals length
proof fn sum_counts_equals_len(s: Seq<Bases>)
    ensures count_occ(s, Bases::A) + count_occ(s, Bases::C) + count_occ(s, Bases::G) + count_occ(s, Bases::T) == s.len()
{
    // Prove by iterating through sequence and accumulating
    let mut a: nat = 0;
    let mut c: nat = 0;
    let mut g: nat = 0;
    let mut t: nat = 0;
    let mut i: int = 0;
    while i < s.len() {
        invariant
// </vc-code>

fn main() {}

}