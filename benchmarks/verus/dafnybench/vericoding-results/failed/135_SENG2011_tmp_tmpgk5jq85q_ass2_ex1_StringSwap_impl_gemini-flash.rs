use vstd::prelude::*;

verus! {

// <vc-helpers>
fn seq_to_vec_char(s: Seq<char>) -> (v: Vec<char>)
    ensures
        v.len() == s.len(),
        forall|k: int| 0 <= k < s.len() ==> v[k as nat] == s[k as nat],
{
    let mut v = Vec::new();
    let mut k: nat = 0;
    while (k as int) < s.len()
        invariant
            (k as int) >= 0 && (k as int) <= s.len(),
            v.len() == k,
            forall|j: int| 0 <= j < (k as int) ==> #[trigger] v[j as nat] == s[j as nat],
    {
        v.push(s[k as nat]);
        k = k + 1;
    }
    v
}

fn vec_char_to_seq(v: &Vec<char>) -> (s: Seq<char>)
    ensures
        s.len() == v.len(),
        forall|k: int| 0 <= k < v.len() ==> s[k as nat] == v[k as nat],
{
    Seq::new(|k: nat| v[k as nat], v.len() as nat)
}
// </vc-helpers>

// <vc-spec>
fn string_swap(s: Seq<char>, i: nat, j: nat) -> (t: Seq<char>)
    requires 
        i >= 0 && j >= 0 && s.len() >= 0,
        s.len() > 0 ==> i < s.len() && j < s.len(),
    ensures 
        s.to_multiset() == t.to_multiset(),
        s.len() == t.len(),
        s.len() > 0 ==> forall|k: nat| k != i && k != j && k < s.len() ==> t[k as int] == s[k as int],
        s.len() > 0 ==> t[i as int] == s[j as int] && t[j as int] == s[i as int],
        s.len() == 0 ==> t == s,
// </vc-spec>
// <vc-code>
{
    if s.len() == 0 {
        return s;
    }

    let mut v = seq_to_vec_char(s);

    if i == j {
        return s;
    }

    // Swap characters at indices i and j
    let temp = v[i as nat];
    proof {
        assert(temp == s[i as int]); // Indexing ghost s with int
        assert(v[j as nat] == s[j as int]); // Indexing ghost s with int
    }
    v.set(i as nat, v[j as nat]);
    proof {
        assert(v@[i as nat] == s[j as int]); // Indexing ghost s with int
    }
    v.set(j as nat, temp);
    proof {
        assert(v@[j as nat] == s[i as int]); // Indexing ghost s with int
    }

    let t = vec_char_to_seq(&v);

    proof {
        // Prove s.to_multiset() == t.to_multiset()
        assert(s.to_multiset() == t.to_multiset());

        // Prove s.len() == t.len()
        assert(s.len() == v.len());
        assert(t.len() == v.len());
        assert(s.len() == t.len());

        // Prove s.len() > 0 ==> forall|k: nat| k != i && k != j && k < s.len() ==> t[k as int] == s[k as int]
        assert forall|k: nat| k != i && k != j && (k as int) < s.len() implies t[k as int] == s[k as int] by {
            let k_int = k as int;
            if k_int != i as int && k_int != j as int && k_int < s.len() {
                assert(vec_char_to_seq(&seq_to_vec_char(s)).ext_equal(s));
                assert(seq_to_vec_char(s).ext_equal(s.to_vec()));
                assert(v.ext_equal(s.to_vec_mut().tracked_read()));

                // We need to show that for k != i and k != j, v[k] is still s[k].
                // The elements in v are from s, but i and j are swapped.
                // We're iterating over k where k is not i and k is not j, so v[k] should be s[k].
                // Since v was initialized from s, and only elements at i and j were changed,
                // for any k not equal to i or j, v[k] is still s[k].
                assert(v[k as nat] == s[k as int]); // v is a Vector, s is a Sequence.
                assert(t[k as int] == v[k as nat]); // t is a Sequence, v is a Vector.
                assert(t[k as int] == s[k as int]); // All good.
            }
        }

        // Prove s.len() > 0 ==> t[i as int] == s[j as int] && t[j as int] == s[i as int]
        assert(t[i as int] == v@[i as nat]);
        assert(v@[i as nat] == s[j as int]);
        assert(t[j as int] == v@[j as nat]);
        assert(v@[j as nat] == s[i as int]);
    }
    t
}
// </vc-code>

// string == Seq<char>
//give se2011 ass2 ex1.dfy

fn main() {}

}