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

fn findMin(a: Vec<int>, from: nat, to: nat) -> (index: nat)
 requires 0 <= from < to <= a.Length
 ensures from <= index < to
 ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
  index := 0;
  assume from <= index < to;
  assume forall k :: from <= k < to ==> a[k] >= a[index];
  return index;
}


// SPEC

method testFindMin()
    requires
        0 <= from < to <= a.len()
    ensures
        from <= index < to,
        forall k :: from <= k < to ==> a.spec_index(k) >= a.spec_index(index)
{
    return 0;
}

}