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
proof fn below_transitive(a: Bases, b: Bases, c: Bases)
    requires
        below(a, b),
        below(b, c),
    ensures
        below(a, c),
{
    // Proof by cases on the values of a, b, c
}

proof fn below_reflexive(a: Bases)
    ensures
        below(a, a),
{
    // Follows directly from definition
}

proof fn exchanger_preserves_below(s: Seq<Bases>, x: nat, y: nat, j: int, k: int)
    requires
        0 < s.len(),
        x < s.len(),
        y < s.len(),
        0 <= j < k < s.len(),
        below(s[j], s[k]),
    ensures
        below(exchanger(s, x, y)[j], exchanger(s, x, y)[k]),
{
    let t = exchanger(s, x, y);
    if j == x as int && k == y as int {
        assert(t[j] == s[y as int]);
        assert(t[k] == s[x as int]);
    } else if j == y as int && k == x as int {
        assert(t[j] == s[x as int]);
        assert(t[k] == s[y as int]);
    } else if j == x as int && k != y as int {
        assert(t[j] == s[y as int]);
        assert(t[k] == s[k]);
    } else if j == y as int && k != x as int {
        assert(t[j] == s[x as int]);
        assert(t[k] == s[k]);
    } else if k == x as int && j != y as int {
        assert(t[j] == s[j]);
        assert(t[k] == s[y as int]);
    } else if k == y as int && j != x as int {
        assert(t[j] == s[j]);
        assert(t[k] == s[x as int]);
    } else {
        assert(t[j] == s[j]);
        assert(t[k] == s[k]);
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
    let mut result = bases;
    let mut a_end: usize = 0;
    let mut c_end: usize = 0;
    let mut g_end: usize = 0;
    let mut current: usize = 0;
    
    while current < result.len() as usize
        invariant
            0 <= a_end <= c_end <= g_end <= current <= result.len(),
            result.len() == bases.len(),
            result.to_multiset() == bases.to_multiset(),
            // Region invariants
            forall|i: int| 0 <= i < a_end ==> result[i] == Bases::A,
            forall|i: int| a_end <= i < c_end ==> result[i] == Bases::C,
            forall|i: int| c_end <= i < g_end ==> result[i] == Bases::G,
            forall|i: int| g_end <= i < current ==> result[i] == Bases::T,
            // Ordering within processed region
            forall|j: int, k: int| 0 <= j < k < current ==> below(result[j], result[k]),
    {
        let current_base = result@[current as int];
        match current_base {
            Bases::A => {
                if current != a_end {
                    result = exchanger(result, a_end, current);
                }
                proof {
                    assert(result[a_end as int] == Bases::A);
                    assert forall|i: int| 0 <= i <= a_end ==> result[i] == Bases::A by {
                        if i < a_end {
                            assert(result[i] == Bases::A);
                        } else {
                            assert(i == a_end);
                            assert(result[i] == Bases::A);
                        }
                    }
                }
                a_end = a_end + 1;
                if c_end < a_end {
                    c_end = a_end;
                }
                if g_end < c_end {
                    g_end = c_end;
                }
                if current < g_end {
                    current = g_end;
                } else {
                    current = current + 1;
                }
            },
            Bases::C => {
                if current != c_end {
                    result = exchanger(result, c_end, current);
                }
                proof {
                    assert(result[c_end as int] == Bases::C);
                }
                c_end = c_end + 1;
                if g_end < c_end {
                    g_end = c_end;
                }
                if current < g_end {
                    current = g_end;
                } else {
                    current = current + 1;
                }
            },
            Bases::G => {
                if current != g_end {
                    result = exchanger(result, g_end, current);
                }
                proof {
                    assert(result[g_end as int] == Bases::G);
                }
                g_end = g_end + 1;
                current = current + 1;
            },
            Bases::T => {
                current = current + 1;
            },
        }
    }
    
    proof {
        assert(current == result.len());
        assert forall|j: int, k: int| 0 <= j < k < result.len() ==> below(result[j], result[k]) by {
            assert(below(result[j], result[k]));
        }
        assert(bordered(result));
    }
    
    result
}
// </vc-code>

fn main() {}

}