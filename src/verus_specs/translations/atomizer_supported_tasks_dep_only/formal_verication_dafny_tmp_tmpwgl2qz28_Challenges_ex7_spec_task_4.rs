// see pdf 'ex6 & 7 documentation' for excercise question

//ATOM_PLACEHOLDER_Bases// SPEC 

//swaps two sequence indexes
pub fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires(0 < s.len() && x < s.len() && y < s.len())
    ensures(|t: Seq<Bases>| t.len() == s.len())
    ensures(|t: Seq<Bases>| forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b])
    ensures(|t: Seq<Bases>| t[x] == s[y] && s[x] == t[y])
    ensures(|t: Seq<Bases>| s.to_multiset() == t.to_multiset())
{
}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
// ATOM 

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
spec fn below(first: Bases, second: Bases) -> bool
{
    first == second ||
    first == Bases::A || 
    (first == Bases::C && (second == Bases::G || second == Bases::T)) || 
    (first == Bases::G && second == Bases::T) ||
    second == Bases::T
}

//checks if a sequence is in base order
// ATOM 

//checks if a sequence is in base order
spec fn bordered(s: Seq<Bases>) -> bool
{
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s[j], s[k])
}

// SPEC 

pub fn Sorter(bases: Seq<Bases>) -> (sobases: Seq<Bases>)
    requires(0 < bases.len())
    ensures(|sobases: Seq<Bases>| sobases.len() == bases.len())
    ensures(|sobases: Seq<Bases>| bordered(sobases))
    ensures(|sobases: Seq<Bases>| bases.to_multiset() == sobases.to_multiset())
{
}

//ATOM_PLACEHOLDER_Testerexchange

// SPEC 

pub fn Testsort()
{
}