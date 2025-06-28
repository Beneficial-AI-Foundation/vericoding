// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StringSwap(s: String, i: nat, j: nat) -> (t: string)
requires i >= 0 && j >= 0 && |s| >= 0
requires |s| > 0 ==> i < |s| && j < |s|
ensures multiset(s[..]) == multiset(t[..])
ensures |s| == |t|
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i]
ensures |s| == 0 ==> t == s
{
  t := "";
  assume multiset(s[..]) ==> multiset(t[..]);
  assume |s| ==> |t|;
  assume |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k];
  assume |s| > 0 ==> t[i] == s[j] && t[j] == s[i];
  assume |s| == 0 ==> t == s;
  return t;
}


// SPEC

method check()
    requires
        i >= 0 && j >= 0 && s.len() >= 0,
        s.len() > 0 ==> i < s.len() && j < s.len()
    ensures
        multiset(s.spec_index(..)) == multiset(t.spec_index(..)),
        s.len() == t.len(),
        s.len() > 0 ==> forall k:nat :: k != i && k != j && k < s.len() ==> t.spec_index(k) == s.spec_index(k),
        s.len() > 0 ==> t.spec_index(i) == s.spec_index(j) && t.spec_index(j) == s.spec_index(i),
        s.len() == 0 ==> t == s
{
    return 0;
}

}