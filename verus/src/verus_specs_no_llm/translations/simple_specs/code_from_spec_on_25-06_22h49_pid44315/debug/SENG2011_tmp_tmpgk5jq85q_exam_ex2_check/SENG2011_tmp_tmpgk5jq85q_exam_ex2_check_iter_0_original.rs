// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Getmini(a: Vec<int>) -> (mini: nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length // mini is an index of a
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
{
  mini := 0;
  assume 0 <= mini < a.Length // mini is an index of a;
  assume forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value;
  assume forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min;
  return mini;
}

/*


// SPEC
method check()
    requires
        a.len() > 0
    ensures
        0 <= mini < a.len() // mini is an index of a,
        forall x :: 0 <= x < a.len() ==> a.spec_index(mini) <= a.spec_index(x) // a.spec_index(mini) is the minimum value,
        forall x :: 0 <= x < mini ==> a.spec_index(mini) < a.spec_index(x) // a.spec_index(mini) is the first min
{
    return 0;
}

}