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
spec fn count_bases(s: Seq<Bases>, base: Bases) -> nat {
    s.filter(|b: Bases| b == base).len()
}

proof fn count_bases_multiset(s: Seq<Bases>, base: Bases)
    ensures
        count_bases(s, base) == s.to_multiset().count(base)
{
    assert(s.filter(|b: Bases| b == base).to_multiset() == s.to_multiset().filter(|b: Bases| b == base));
    assert(s.to_multiset().filter(|b: Bases| b == base).len() == s.to_multiset().count(base));
}

proof fn multiset_count_preserved(s1: Seq<Bases>, s2: Seq<Bases>)
    requires
        s1.to_multiset() == s2.to_multiset()
    ensures
        forall|base: Bases| count_bases(s1, base) == count_bases(s2, base)
{
    assert forall|base: Bases| count_bases(s1, base) == count_bases(s2, base) by {
        count_bases_multiset(s1, base);
        count_bases_multiset(s2, base);
    };
}

proof fn exchanger_preserves_count(s: Seq<Bases>, x: nat, y: nat)
    requires
        0 < s.len(), x < s.len(), y < s.len()
    ensures
        forall|base: Bases| count_bases(exchanger(s, x, y), base) == count_bases(s, base)
{
    let t = exchanger(s, x, y);
    assert(t.to_multiset() == s.to_multiset());
    multiset_count_preserved(s, t);
}

spec fn is_partitioned(s: Seq<Bases>, i: int) -> bool {
    forall|j: int| 0 <= j < i ==> below(s[j], s[i])
}

proof fn below_transitive(a: Bases, b: Bases, c: Bases)
    requires
        below(a, b), below(b, c)
    ensures
        below(a, c)
{
}

proof fn below_reflexive(a: Bases)
    ensures
        below(a, a)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sorter(bases: Seq<Bases>) -> (sobases: Seq<Bases>)
    requires 
        0 < bases.len()
    ensures 
        sobases.len() == bases.len(),
        bordered(sobases),
        bases.to_multiset() == sobases.to_multiset()
// </vc-spec>
// </vc-spec>

// <vc-code>
fn exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires
        0 < s.len(), x < s.len(), y < s.len()
    ensures
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b],
        t[x as int] == s[y as int] && t[y as int] == s[x as int],
        s.to_multiset() == t.to_multiset()
{
    let mut result = s;
    let temp = result[x as int];
    result = result.update(x as int, result[y as int]);
    result = result.update(y as int, temp);
    result
}

fn sorter(bases: Seq<Bases>) -> (sobases: Seq<Bases>)
    requires
        0 < bases.len()
    ensures
        sobases.len() == bases.len(),
        bordered(sobases),
        bases.to_multiset() == sobases.to_multiset()
{
    let mut result = bases;
    let len = bases.len();
    let mut i: int = 0;
    while i < len as int
        invariant
            0 <= i <= len as int,
            result.len() == len,
            bases.to_multiset() == result.to_multiset(),
            bordered(result.subrange(0, i))
    {
        let mut j = i + 1;
        while j < len as int
            invariant
                0 <= i < len as int,
                i < j <= len as int,
                result.len() == len,
                bases.to_multiset() == result.to_multiset(),
                bordered(result.subrange(0, i)),
                forall|k: int| i < k < j ==> !below(result[k], result[i])
        {
            if !below(result[j], result[i]) {
                result = exchanger(result, i as nat, j as nat);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}