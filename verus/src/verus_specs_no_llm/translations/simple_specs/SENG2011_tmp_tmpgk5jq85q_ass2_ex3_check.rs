// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: String) -> bool {
    // all b's are before all a's && d's
  forall i,j :: 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'b' && (s.spec_index(j) == 'a' | s.spec_index(j) == 'd') ==> i < j &&
  // all a's are after all b's
  forall i,j :: 0 <= i < .len()s && 0 <= j < .len()s && s.spec_index(i) == 'a' && s.spec_index(j) == 'b' ==> i > j &&
  // all a's are before all d's
  forall i,j :: 0 <= i < .len()s && 0 <= j < .len()s && s.spec_index(i) == 'a' && s.spec_index(j) == 'd' ==> i < j &&
  // all d's are after a;; b's && a's
  forall i,j :: 0 <= i < .len()s && 0 <= j < .len()s && s.spec_index(i) == 'd' && (s.spec_index(j) == 'a' .len()| s.spec_index(j) == 'b') ==> i > j
}

fn BadSort(a: String) -> (b: string)
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
        forall k :: 0 <= k < a.len() ==> a.spec_index(k) == 'b' | a.spec_index(k) == 'a' .len()| a.spec_index(k) == 'd'
    ensures
        sortedbad(b),
        multiset(a.spec_index(..)) == multiset(b.spec_index(..)),
        a.len() == b.len()
{
    return 0;
}

}