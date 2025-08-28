use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn seq_swap<T>(s: Seq<T>, i: nat, j: nat) -> Seq<T>
    recommends i < s.len(), j < s.len()
{
    s.update(i as int, s[j as int]).update(j as int, s[i as int])
}

proof fn lemma_seq_swap_multiset<T>(s: Seq<T>, i: nat, j: nat)
    requires i < s.len(), j < s.len()
    ensures seq_swap(s, i, j).to_multiset() == s.to_multiset()
{
    let t = seq_swap(s, i, j);
    if i == j {
        assert(t == s);
    } else {
        assert(t.to_multiset() =~= s.to_multiset());
    }
}

proof fn lemma_seq_swap_len<T>(s: Seq<T>, i: nat, j: nat)
    requires i < s.len(), j < s.len()
    ensures seq_swap(s, i, j).len() == s.len()
{
}

proof fn lemma_seq_swap_other_indices<T>(s: Seq<T>, i: nat, j: nat, k: nat)
    requires i < s.len(), j < s.len(), k != i, k != j, k < s.len()
    ensures seq_swap(s, i, j)[k as int] == s[k as int]
{
}

proof fn lemma_seq_swap_swapped_indices<T>(s: Seq<T>, i: nat, j: nat)
    requires i < s.len(), j < s.len()
    ensures 
        seq_swap(s, i, j)[i as int] == s[j as int],
        seq_swap(s, i, j)[j as int] == s[i as int]
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    if s.len() == 0 {
        s
    } else {
        let t = seq_swap(s, i, j);
        proof {
            lemma_seq_swap_multiset(s, i, j);
            lemma_seq_swap_len(s, i, j);
            lemma_seq_swap_swapped_indices(s, i, j);
            assert forall|k: nat| k != i && k != j && k < s.len() implies t[k as int] == s[k as int] by {
                lemma_seq_swap_other_indices(s, i, j, k);
            }
        }
        t
    }
}
// </vc-code>

// string == Seq<char>
//give se2011 ass2 ex1.dfy

fn main() {}

}