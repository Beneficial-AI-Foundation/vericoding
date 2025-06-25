use vstd::prelude::*;

verus! {

// ATOM 

spec fn derangement(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != i
}

//ATOM_PLACEHOLDER_permutation

// ATOM 

spec fn multisetRange(n: nat) -> Multiset<nat> {
    Seq::new(n, |i: int| i as nat).to_multiset()
}

//ATOM_PLACEHOLDER_distinct

// SPEC 

pub fn test() {
}

//ATOM_PLACEHOLDER_unknown_522 

pub fn end(links: Seq<nat>)
    requires(links.len() > 0)
    requires(permutation(links))
    requires(derangement(links))
    requires(distinct(links))
{
}

}