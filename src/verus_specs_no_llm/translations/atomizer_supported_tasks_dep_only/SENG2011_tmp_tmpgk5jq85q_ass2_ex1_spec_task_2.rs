// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn StringSwap(s: String, i: nat, j: nat) -> (t: String)
    requires i >= 0 and j >= 0 and s.len() >= 0;,
             s.len() > 0 ==> i < s.len() and j < s.len();
    ensures multiset(s[..]) == multiset(t[..]);,
            s.len() == t.len();,
            s.len() > 0 ==> forall k:nat :: k != i and k != j and k < s.len() ==> t[k] == s[k],
            s.len() > 0 ==> t[i] == s[j] and t[j] == s[i];,
            s.len() == 0 ==> t == s;
{
}

}