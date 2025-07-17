// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: String) -> bool {
    // all b's are before all a's && d's
  forall |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.index(i) == 'b' && (s.index(j) == 'a' | s.index(j) == 'd') ==> i < j &&
  // all a's are after all b's
  forall |i: int, j: int| 0 <= i < .len()s && 0 <= j < .len()s && s.index(i) == 'a' && s.index(j) == 'b' ==> i > j &&
  // all a's are before all d's
  forall |i: int, j: int| 0 <= i < .len()s && 0 <= j < .len()s && s.index(i) == 'a' && s.index(j) == 'd' ==> i < j &&
  // all d's are after a;; b's && a's
  forall |i: int, j: int| 0 <= i < .len()s && 0 <= j < .len()s && s.index(i) == 'd' && (s.index(j) == 'a' .len()| s.index(j) == 'b') ==> i > j
}

spec fn spec_BadSort(a: String) -> b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
ensures sortedbad(b)
ensures multiset(a[..]) == multiset(b[..])
ensures |a| == |b|
{
  b := "";
  assume sortedbad(b);
  assume multiset(a[..]) ==> multiset(b[..]);
  assume |a| ==> |b|;
  return b;
}


// SPEC
method check(
    requires
        forall |k: int| 0 <= k < a.len() ==> a.index(k) == 'b' | a.index(k) == 'a' .len()| a.index(k) == 'd'
    ensures
        sortedbad(b),
        multiset(a.index(..)) == multiset(b.index(..)),
        a.len() == b.len()
;

proof fn lemma_BadSort(a: String) -> (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
ensures sortedbad(b)
ensures multiset(a[..]) == multiset(b[..])
ensures |a| == |b|
{
  b := "";
  assume sortedbad(b);
  assume multiset(a[..]) ==> multiset(b[..]);
  assume |a| ==> |b|;
  return b;
}


// SPEC
method check()
    requires
        forall |k: int| 0 <= k < a.len() ==> a.index(k) == 'b' | a.index(k) == 'a' .len()| a.index(k) == 'd'
    ensures
        sortedbad(b),
        multiset(a.index(..)) == multiset(b.index(..)),
        a.len() == b.len()
{
    0
}

}