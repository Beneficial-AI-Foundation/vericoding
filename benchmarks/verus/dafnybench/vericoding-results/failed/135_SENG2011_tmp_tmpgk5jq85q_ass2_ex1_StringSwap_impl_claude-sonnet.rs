use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_multiset_swap(s: Seq<char>, t: Seq<char>, i: nat, j: nat)
    requires
        i < s.len(),
        j < s.len(),
        s.len() == t.len(),
        t[i as int] == s[j as int],
        t[j as int] == s[i as int],
        forall|k: nat| k != i && k != j && k < s.len() ==> t[k as int] == s[k as int],
    ensures
        s.to_multiset() == t.to_multiset(),
{
    assert(s.to_multiset().count(s[i as int]) == t.to_multiset().count(s[i as int]));
    assert(s.to_multiset().count(s[j as int]) == t.to_multiset().count(s[j as int]));
    assert(forall|c: char| s.to_multiset().count(c) == t.to_multiset().count(c));
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
    if s.len() == 0nat {
        s
    } else {
        let ghost t1 = s.update(i as int, s[j as int]);
        let ghost t = t1.update(j as int, s[i as int]);
        
        proof {
            lemma_multiset_swap(s, t, i, j);
        }
        
        t
    }
}
// </vc-code>

// string == Seq<char>
//give se2011 ass2 ex1.dfy

fn main() {}

}