// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_StringSwap(s: String, i: nat, j: nat) -> t: string)
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

method check(
    requires
        i >= 0 && j >= 0 && s.len() >= 0,
        s.len() > 0 ==> i < s.len() && j < s.len()
    ensures
        multiset(s.index(..)) == multiset(t.index(..)),
        s.len() == t.len(),
        s.len() > 0 ==> forall |k: nat| k != i && k != j && k < s.len() ==> t.index(k) == s.index(k),
        s.len() > 0 ==> t.index(i) == s.index(j) && t.index(j) == s.index(i),
        s.len() == 0 ==> t == s
;

proof fn lemma_StringSwap(s: String, i: nat, j: nat) -> (t: string)
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
        multiset(s.index(..)) == multiset(t.index(..)),
        s.len() == t.len(),
        s.len() > 0 ==> forall |k: nat| k != i && k != j && k < s.len() ==> t.index(k) == s.index(k),
        s.len() > 0 ==> t.index(i) == s.index(j) && t.index(j) == s.index(i),
        s.len() == 0 ==> t == s
{
    0
}

}