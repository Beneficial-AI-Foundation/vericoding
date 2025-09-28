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
spec fn count_in_range(s: Seq<Bases>, lo: nat, hi: nat, target: Bases) -> nat
    recommends lo <= hi <= s.len()
{
    if hi <= lo {
        0
    } else {
        count_in_range(s, lo, (hi - 1) as nat, target) + (if s[(hi - 1) as int] == target { 1nat } else { 0nat })
    }
}

proof fn below_transitive()
    ensures
        forall|a: Bases, b: Bases, c: Bases| below(a, b) && below(b, c) ==> below(a, c)
{
    assert forall|a: Bases, b: Bases, c: Bases| below(a, b) && below(b, c) implies below(a, c) by {
        match (a, b, c) {
            (Bases::A, _, _) => assert(below(a, c)),
            (Bases::C, Bases::C, _) => assert(below(a, c)),
            (Bases::C, Bases::G, Bases::G) => assert(below(a, c)),
            (Bases::C, Bases::G, Bases::T) => assert(below(a, c)),
            (Bases::C, Bases::T, Bases::T) => assert(below(a, c)),
            (Bases::G, Bases::G, _) => assert(below(a, c)),
            (Bases::G, Bases::T, Bases::T) => assert(below(a, c)),
            (Bases::T, Bases::T, _) => assert(below(a, c)),
            _ => assert(false),
        }
    };
}

proof fn below_reflexive()
    ensures
        forall|a: Bases| below(a, a)
{
    assert forall|a: Bases| below(a, a) by {
        assert(a == a);
    };
}

spec fn partitioned(s: Seq<Bases>, i: nat, j: nat, k: nat, l: nat) -> bool
    recommends i <= j <= k <= l <= s.len()
{
    forall|idx: int| 0 <= idx < i ==> s[idx] == Bases::A &&
    forall|idx: int| i <= idx < j ==> s[idx] == Bases::C &&
    forall|idx: int| j <= idx < k ==> s[idx] == Bases::G &&
    forall|idx: int| k <= idx < l ==> s[idx] == Bases::T
}

proof fn partitioned_implies_bordered(s: Seq<Bases>, i: nat, j: nat, k: nat, l: nat)
    requires
        partitioned(s, i, j, k, l),
        l == s.len()
    ensures
        bordered(s)
{
    below_transitive();
    below_reflexive();
    assert forall|m: int, n: int| 0 <= m < n < s.len() implies below(s[m], s[n]) by {
        if m < i as int {
            if n < i as int { assert(s[m] == Bases::A && s[n] == Bases::A); }
            else if n < j as int { assert(s[m] == Bases::A && s[n] == Bases::C); }
            else if n < k as int { assert(s[m] == Bases::A && s[n] == Bases::G); }
            else { assert(s[m] == Bases::A && s[n] == Bases::T); }
        } else if m < j as int {
            if n < j as int { assert(s[m] == Bases::C && s[n] == Bases::C); }
            else if n < k as int { assert(s[m] == Bases::C && s[n] == Bases::G); }
            else { assert(s[m] == Bases::C && s[n] == Bases::T); }
        } else if m < k as int {
            if n < k as int { assert(s[m] == Bases::G && s[n] == Bases::G); }
            else { assert(s[m] == Bases::G && s[n] == Bases::T); }
        } else {
            assert(s[m] == Bases::T && s[n] == Bases::T);
        }
    };
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
    let mut v: Vec<Bases> = Vec::new();
    let n = bases.len();
    proof {
        v = Vec::<Bases>::from_seq(bases);
    }
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut k: usize = 0;
    let mut l: usize = n;
    
    proof {
        partitioned_implies_bordered(bases, 0, 0, 0, n as nat);
    }
    
    while k < l
        invariant
            i <= j <= k <= l <= n,
            partitioned(v@, i as nat, j as nat, k as nat, l as nat),
            v@.to_multiset() == bases.to_multiset(),
    {
        let current = v[k];
        match current {
            Bases::A => {
                let temp = v[i];
                v[i] = Bases::A;
                v[k] = temp;
                proof {
                    assert(v@.to_multiset() == bases.to_multiset());
                }
                i += 1;
                j += 1;
                k += 1;
            }
            Bases::C => {
                let temp = v[j];
                v[j] = Bases::C;
                v[k] = temp;
                proof {
                    assert(v@.to_multiset() == bases.to_multiset());
                }
                j += 1;
                k += 1;
            }
            Bases::G => {
                k += 1;
            }
            Bases::T => {
                l -= 1;
                let temp = v[k];
                v[k] = v[l];
                v[l] = temp;
                proof {
                    assert(v@.to_multiset() == bases.to_multiset());
                }
            }
        }
    }
    
    proof {
        partitioned_implies_bordered(v@, i as nat, j as nat, k as nat, l as nat);
        assert(l == n);
    }
    
    v.into_seq()
}
// </vc-code>

fn main() {}

}