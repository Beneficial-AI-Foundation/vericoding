// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>, a
{
  forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}


// SPEC




method Main() -> bool {
    var x := new int.spec_index(10);
  x.spec_index(0), x.spec_index(1), x.spec_index(2), x.spec_index(3) := 2, 2, 1, 5;
  var y := sum(x, 0, x.len());
  //assert y == 10;
  var c := new int.spec_index(11);
  c.spec_index(0), c.spec_index(1), c.spec_index(2), c.spec_index(3), c.spec_index(4) := 0, 2, 4, 5, 10;
  // var r := queryFast(x, c, 0, x.len())
}

}