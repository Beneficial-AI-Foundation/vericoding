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
fn exchanger_spec(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 
        0 < s.len() && x < s.len() && y < s.len()
    ensures 
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x as int && b != y as int ==> t[b] == s[b],
        t[x as int] == s[y as int] && s[x as int] == t[y as int],
        s.to_multiset() == t.to_multiset()
{
    let mut a = s.to_vec();
    a.swap_unchecked(x as usize, y as usize);
    a.to_seq()
}

spec fn count_bases(s: Seq<Bases>, base: Bases) -> nat {
    (0..s.len()).filter(|i| s[i] == base).count() as nat
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
    let mut a: Vec<Bases> = bases.to_vec();

    let mut current: nat = 0;
    let mut next_A: nat = 0;
    let mut next_C: nat = 0;
    let mut next_G: nat = 0;
    let mut next_T_idx: nat = (a.len() - 1) as nat; 

    while current <= next_T_idx
        invariant
            0 <= current,
            current <= a.len(), 
            0 <= next_A <= current,
            0 <= next_A <= next_C,
            0 <= next_C <= next_G,
            0 <= next_G <= current,
            next_T_idx < a.len(),
            forall|k: int| 0 <= k < next_A as int ==> a[k] == Bases::A,
            forall|k: int| next_A as int <= k < next_C as int ==> a[k] == Bases::C,
            forall|k: int| next_C as int <= k < next_G as int ==> a[k] == Bases::G,
            forall|k: int| next_G as int <= k < current as int ==> a[k] == Bases::T,
            forall|k: int| (next_T_idx + 1) as int <= k < a.len() as int ==> a[k] == Bases::T,
            a.to_seq().to_multiset() == bases.to_multiset(),
            a.len() == bases.len(),
    {
        let current_base = a[current as usize];
        match current_base {
            Bases::A => {
                proof {
                    let s_pre = a.to_seq();
                    let x = current;
                    let y = next_A;
                    assert(s_pre.len() > 0);
                    assert(x < s_pre.len());
                    assert(y < s_pre.len());
                    assert(exchanger_spec(s_pre, x, y).to_multiset() == s_pre.to_multiset());
                }
                a.swap(current as usize, next_A as usize);
                current = current + 1;
                next_A = next_A + 1;
                if next_C < next_A { next_C = next_A; }
                if next_G < next_C { next_G = next_C; }
            },
            Bases::C => {
                proof {
                    let s_pre = a.to_seq();
                    let x = current;
                    let y = next_C;
                    assert(s_pre.len() > 0);
                    assert(x < s_pre.len());
                    assert(y < s_pre.len());
                    assert(exchanger_spec(s_pre, x, y).to_multiset() == s_pre.to_multiset());
                }
                a.swap(current as usize, next_C as usize);
                current = current + 1;
                next_C = next_C + 1;
                if next_G < next_C { next_G = next_C; }
            },
            Bases::G => {
                proof {
                    let s_pre = a.to_seq();
                    let x = current;
                    let y = next_G;
                    assert(s_pre.len() > 0);
                    assert(x < s_pre.len());
                    assert(y < s_pre.len());
                    assert(exchanger_spec(s_pre, x, y).to_multiset() == s_pre.to_multiset());
                }
                a.swap(current as usize, next_G as usize);
                current = current + 1;
                next_G = next_G + 1;
            },
            Bases::T => {
                proof {
                    let s_pre = a.to_seq();
                    let x = current;
                    let y = next_T_idx as nat;
                    assert(s_pre.len() > 0);
                    assert(x < s_pre.len());
                    assert(y < s_pre.len());
                    assert(exchanger_spec(s_pre, x, y).to_multiset() == s_pre.to_multiset());
                }
                a.swap(current as usize, next_T_idx as usize);
                next_T_idx = next_T_idx - 1;
            },
        }
    }

    let final_seq = a.to_seq();

    proof {
        assert(final_seq.len() == bases.len());
        assert(final_seq.to_multiset() == bases.to_multiset());

        assert forall|j: int, k: int| 0 <= j < k < final_seq.len() implies below(final_seq[j], final_seq[k]) by {
            let sj_val = final_seq[j];
            let sk_val = final_seq[k];

            if (j as nat) < next_A { // Bases::A section
                assert(sj_val == Bases::A);
            } else if (j as nat) < next_C { // Bases::C section
                assert(sj_val == Bases::C);
            } else if (j as nat) < next_G { // Bases::G section
                assert(sj_val == Bases::G);
            } else { // Bases::T section
                assert(sj_val == Bases::T);
            }

            if (k as nat) < next_A { // Bases::A section
                assert(sk_val == Bases::A);
            } else if (k as nat) < next_C { // Bases::C section
                assert(sk_val == Bases::C);
            } else if (k as nat) < next_G { // Bases::G section
                assert(sk_val == Bases::G);
            } else { // Bases::T section
                assert(sk_val == Bases::T);
            }

            assert(below(sj_val, sk_val));
        }
    }

    final_seq
}
// </vc-code>

fn main() {}

}