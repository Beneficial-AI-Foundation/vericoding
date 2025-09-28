use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_swap_elements<T>(seq: Seq<T>, i: int, j: int)
    requires
        0 <= i < seq.len(),
        0 <= j < seq.len(),
    ensures
        seq.update(i, seq[j]).update(j, seq[i]) == seq.update(j, seq[i]).update(i, seq[j]),
{
    assert(forall|k: int|
        0 <= k < seq.len() ==>
        seq.update(i, seq[j]).update(j, seq[i])[k] ==
        if k == i {
            seq[j]
        } else if k == j {
            seq[i]
        } else {
            seq[k]
        });
    assert(forall|k: int|
        0 <= k < seq.len() ==>
        seq.update(j, seq[i]).update(i, seq[j])[k] ==
        if k == j {
            seq[i]
        } else if k == i {
            seq[j]
        } else {
            seq[k]
        });
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
        s
    } else {
        proof {
            lemma_swap_elements(s, i, j);
        }
        let result = s.update(i, s[j]).update(j, s[i]);
        result
    }
}
// </vc-code>

// string == Seq<char>
//give se2011 ass2 ex1.dfy

fn main() {}

}