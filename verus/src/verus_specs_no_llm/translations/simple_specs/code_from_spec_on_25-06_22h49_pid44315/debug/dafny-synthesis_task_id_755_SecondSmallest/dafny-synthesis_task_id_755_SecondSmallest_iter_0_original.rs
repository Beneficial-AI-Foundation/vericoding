// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SecondSmallest(s: Vec<int>) -> (secondSmallest: int)
    requires
        s.len() >= 2
  // There must be at least 2 different values, a minimum && another one,
        exists i, j :: 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.spec_index(i) == min(s.spec_index(..)) && s.spec_index(j) != s.spec_index(i)
    ensures
        exists i, j :: 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.spec_index(i) == min(s.spec_index(..)) && s.spec_index(j) == secondSmallest,
        forall k :: 0 <= k < s.len() && s.spec_index(k) != min(s.spec_index(..)) ==> s.spec_index(k) >= secondSmallest
{
    return 0;
}

}