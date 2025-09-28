use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
        let mut t = s;
        let temp_i = s@[i as int];
        let temp_j = s@[j as int];
        t = t.update(i as int, temp_j);
        t = t.update(j as int, temp_i);
        t
    }
}
// </vc-code>

// string == Seq<char>
//give se2011 ass2 ex1.dfy

fn main() {}

}