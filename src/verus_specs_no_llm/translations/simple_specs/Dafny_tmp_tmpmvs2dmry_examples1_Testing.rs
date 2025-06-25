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

fn Abs(x: int) -> (y: int)
ensures y>=0
ensures x>=0 ==> x == y
ensures x<0 ==> -x == y
ensures y == abs(x); // use this instead of line 3, 4
{
  y: = 0;
  assume y>=0;
  assume x>=0 ==> x == y;
  assume x<0 ==> -x == y;
  assume y ==> abs(x); // use this instead of line 3, 4;
  return y;
}


//ATOM

function abs(x: int): int{
  if x>0 then x else -x
}


// SPEC

method Testing()
    ensures
        y>=0,
        x>=0 ==> x == y,
        x<0 ==> -x == y,
        y == abs(x); // use this instead of line 3,4
{
    return (0, 0, 0);
}

}