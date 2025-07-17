// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn min(s: Seq<int>) -> (r: int)
    requires
        s.len() >= 2
    ensures
        forall |i: int| 0 <= i < s.len() ==> r <= s.index(i)
{
    0
}

spec fn spec_SecondSmallest(s: Vec<int>) -> secondSmallest: int
    requires
        s.len() >= 2
  // There must be at least 2 different values, a minimum && another one,
        exists |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.index(i) == min(s.index(..)) && s.index(j) != s.index(i)
    ensures
        exists |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.index(i) == min(s.index(..)) && s.index(j) == secondSmallest,
        forall |k: int| 0 <= k < s.len() && s.index(k) != min(s.index(..)) ==> s.index(k) >= secondSmallest
;

proof fn lemma_SecondSmallest(s: Vec<int>) -> (secondSmallest: int)
    requires
        s.len() >= 2
  // There must be at least 2 different values, a minimum && another one,
        exists |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.index(i) == min(s.index(..)) && s.index(j) != s.index(i)
    ensures
        exists |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.index(i) == min(s.index(..)) && s.index(j) == secondSmallest,
        forall |k: int| 0 <= k < s.len() && s.index(k) != min(s.index(..)) ==> s.index(k) >= secondSmallest
{
    0
}

}