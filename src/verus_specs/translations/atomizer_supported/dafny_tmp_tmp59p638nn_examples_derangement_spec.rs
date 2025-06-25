use vstd::prelude::*;

verus! {

// ATOM 

spec fn derangement(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != i
}

// ATOM 

spec fn permutation(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s.contains(i)
}

// ATOM 

spec fn multisetRange(n: nat) -> Multiset<nat> {
    Seq::new(n, |i: int| i).to_multiset()
}

// ATOM 

spec fn distinct<A>(s: Seq<A>) -> bool {
    forall|x: int, y: int| x != y && 0 <= x <= y < s.len() ==> s[x] != s[y]
}

// SPEC 

pub fn test() {
}

pub fn end(links: Seq<nat>)
    requires(|links| > 0)
    requires(permutation(links))
    requires(derangement(links))
    requires(distinct(links))
{
}

}