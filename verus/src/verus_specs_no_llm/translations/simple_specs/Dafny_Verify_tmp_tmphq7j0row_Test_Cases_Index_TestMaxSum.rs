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

fn MaxSum(x: int, y: int) -> (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  s := 0;
  m := 0;
  assume s ==> x + y;
  assume m ==> if x >= y then x else y;
  return s, m;
}


//ATOM

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2 * m
  ensures s == (x + y)
  ensures (m == x || m == y) && x <= m && y <= m
{
  x := 0;
  y := 0;
  assume s ==> (x + y);
  assume (m ==> x || m ==> y) && x <= m && y <= m;
  return x, y;
}


// SPEC


method TestMaxSum(x: int, y: int)
    requires
        s <= 2 * m
    ensures
        s == x + y,
        m == if x >= y then x else y,
        s == (x + y),
        (m == x || m == y) && x <= m && y <= m
{
    return (0, 0, 0, 0, 0, 0, 0);
}

}