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
fn exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 
        0 < s.len() && x < s.len() && y < s.len()
    ensures 
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b],
        t[x as int] == s[y as int] && s[x as int] == t[y as int],
        s.to_multiset() == t.to_multiset()
{
    if x == y {
        s
    } else {
        let mut t = s;
        t = t.update(x as int, s[y as int]);
        t = t.update(y as int, s[x as int]);
        t
    }
}

proof fn lemma_below_transitive(a: Bases, b: Bases, c: Bases)
    requires
        below(a, b),
        below(b, c),
    ensures
        below(a, c)
{
    match (a, b, c) {
        (Bases::A, _, _) => {},
        (_, Bases::T, _) => {},
        (Bases::C, Bases::C, _) => {},
        (Bases::C, Bases::G, Bases::G) => {},
        (Bases::C, Bases::G, Bases::T) => {},
        (Bases::G, Bases::G, _) => {},
        _ => assert(false),
    }
}

proof fn lemma_below_swap_none(s: Seq<Bases>, x: nat, y: nat, i: nat, j: nat)
    requires
        0 < s.len(),
        x < s.len(),
        y < s.len(),
        i < j,
        j < s.len(),
        below(s[j], s[i]),
        i != x && i != y,
        j != x && j != y,
    ensures
        let t = exchanger(s, x, y);
        below(t[j], t[i])
{
    assert(exchanger(s, x, y)[j] == s[j] && exchanger(s, x, y)[i] == s[i]);
}

proof fn lemma_below_swap_first(s: Seq<Bases>, x: nat, y: nat, i: nat, j: nat)
    requires
        0 < s.len(),
        x < s.len(),
        y < s.len(),
        i < j,
        j < s.len(),
        below(s[j], s[i]),
        i == x && j != y,
    ensures
        let t = exchanger(s, x, y);
        below(t[j], t[i])
{
    assert(exchanger(s, x, y)[j] == s[j]);
    assert(exchanger(s, x, y)[i] == s[y]);
    assert(below(s[j], s[y]));
    lemma_below_transitive(s[j], s[y], s[i]);
}

proof fn lemma_below_swap_second(s: Seq<Bases>, x: nat, y: nat, i: nat, j: nat)
    requires
        0 < s.len(),
        x < s.len(),
        y < s.len(),
        i < j,
        j < s.len(),
        below(s[j], s[i]),
        i != x && j == y,
    ensures
        let t = exchanger(s, x, y);
        below(t[j], t[i])
{
    assert(exchanger(s, x, y)[j] == s[x]);
    assert(exchanger(s, x, y)[i] == s[i]);
    assert(below(s[x], s[i]));
}

proof fn lemma_below_swap_both(s: Seq<Bases>, x: nat, y: nat, i: nat, j: nat)
    requires
        0 < s.len(),
        x < s.len(),
        y < s.len(),
        i < j,
        j < s.len(),
        below(s[j], s[i]),
        i == x && j == y,
    ensures
        let t = exchanger(s, x, y);
        below(t[j], t[i])
{
    assert(exchanger(s, x, y)[j] == s[x]);
    assert(exchanger(s, x, y)[i] == s[y]);
    lemma_below_transitive(s[x], s[y], s[x]);
}

proof fn lemma_bordered_swap_preserves(s: Seq<Bases>, x: nat, y: nat)
    requires
        0 < s.len(),
        x < s.len(),
        y < s.len(),
        bordered(s),
    ensures
        bordered(exchanger(s, x, y))
{
    assert(bordered(exchanger(s, x, y))) by {
        forall|i: int, j: int| 
            #[trigger]
            0 <= i < j < s.len()
        ensures
            below(exchanger(s, x, y)[j], exchanger(s, x, y)[i])
        {
            if i == x && j == y {
                lemma_below_swap_both(s, x, y, i, j);
            } else if i == x && j != y {
                lemma_below_swap_first(s, x, y, i, j);
            } else if i != x && j == y {
                lemma_below_swap_second(s, x, y, i, j);
            } else {
                lemma_below_swap_none(s, x, y, i, j);
            }
        }
    }
}

proof fn lemma_subrange_bordered(s: Seq<Bases>, a: nat, b: nat)
    requires
        0 <= a <= b <= s.len(),
        bordered(s),
    ensures
        bordered(s.subrange(a as int, b as int))
{
    assert(bordered(s.subrange(a as int, b as int))) by {
        forall|i: int, j: int|
            #[trigger]
            0 <= i < j < (b - a)
        ensures
            below(s.subrange(a as int, b as int)[j], s.subrange(a as int, b as int)[i])
        {
            assert(s.subrange(a as int, b as int)[i] == s[a + i]);
            assert(s.subrange(a as int, b as int)[j] == s[a + j]);
            assert(0 <= a + i < a + j < s.len());
            assert(below(s[a + j], s[a + i]));
        }
    }
}

proof fn lemma_bordered_prefix_suffix(s: Seq<Bases>, a: nat)
    requires
        0 <= a <= s.len(),
        forall|i: int, j: int| 0 <= i < j < a ==> below(s[j], s[i]),
        bordered(s.subrange(a as int, s.len() as int)),
    ensures
        bordered(s)
{
    assert(bordered(s)) by {
        forall|i: int, j: int|
            #[trigger]
            0 <= i < j < s.len()
        ensures
            below(s[j], s[i])
        {
            if j < a {
                assert(below(s[j], s[i]));
            } else if i >= a {
                assert(below(s[j], s[i])) by {
                    assert(s[i] == s.subrange(a as int, s.len() as int)[i - a]);
                    assert(s[j] == s.subrange(a as int, s.len() as int)[j - a]);
                    assert(0 <= i - a < j - a < s.len() - a);
                    assert(bordered(s.subrange(a as int, s.len() as int)));
                    assert(below(s.subrange(a as int, s.len() as int)[j - a], s.subrange(a as int, s.len() as int)[i - a]));
                }
            } else {
                assert(i < a && j >= a);
                assert(below(s[j], s[i])) by {
                    assert(below(s[j], s[a])) by {
                        assert(s[j] == s.subrange(a as int, s.len() as int)[j - a]);
                        assert(s[a] == s.subrange(a as int, s.len() as int)[0]);
                        assert(0 <= 0 <= j - a < s.len() - a);
                        assert(bordered(s.subrange(a as int, s.len() as int)));
                        assert(below(s.subrange(a as int, s.len() as int)[j - a], s.subrange(a as int, s.len() as int)[0]));
                    }
                    assert(below(s[a], s[i])) by {
                        assert(below(s[a], s[i]));
                    }
                    lemma_below_transitive(s[j], s[a], s[i]);
                }
            }
        }
    }
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
    let mut sorted_bases = bases;
    let n = bases.len();
    
    for a in 0..n
        invariant
            n == sorted_bases.len(),
            sorted_bases.to_multiset() == bases.to_multiset(),
            forall|i: int, j: int| 0 <= i < j < a ==> below(sorted_bases[j], sorted_bases[i]),
            bordered(sorted_bases.subrange(a as int, n as int))
    {
        let mut min_index = a;
        
        for b in (a + 1)..n
            invariant
                a < b,
                a <= min_index < b,
                forall|i: int| a <= i < b ==> below(sorted_bases[min_index as int], sorted_bases[i]) || sorted_bases[min_index as int] == sorted_bases[i],
                forall|i: int, j: int| 0 <= i < j < a ==> below(sorted_bases[j], sorted_bases[i]),
                bordered(sorted_bases.subrange(a as int, n as int))
        {
            if !below(sorted_bases[b as int], sorted_bases[min_index as int]) {
                min_index = b;
                proof {
                    assert(forall|i: int| a <= i < b 
                        ==> below(sorted_bases[min_index as int], sorted_bases[i]) || sorted_bases[min_index as int] == sorted_bases[i]);
                }
            }
        }
        
        if min_index != a {
            sorted_bases = exchanger(sorted_bases, a, min_index);
            proof {
                assert(sorted_bases.to_multiset() == bases.to_multiset());
                
                assert(forall|i: int, j: int| 0 <= i < j < a ==> below(sorted_bases[j], sorted_bases[i]));
                
                lemma_bordered_swap_preserves(sorted_bases, a, min_index);
            }
        }
    }
    
    sorted_bases
}
// </vc-code>

fn main() {}

}