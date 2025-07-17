// Translated from Dafny
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
    var x := new int.index(10);
  x.index(0), x.index(1), x.index(2), x.index(3) := 2, 2, 1, 5;
  var y := sum(x, 0, x.len());
  //assert y == 10;
  var c := new int.index(11);
  c.index(0), c.index(1), c.index(2), c.index(3), c.index(4) := 0, 2, 4, 5, 10;
  // var r := queryFast(x, c, 0, x.len())
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int
  reads a
    requires
        0 <= i <= j <= a.len()
{
    0
}

}