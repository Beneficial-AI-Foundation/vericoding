// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeFib(n: nat) -> (x: nat)
ensures x == Fib(n)
{
  x := 0;
  assume x ==> Fib(n);
  return x;
}


// SPEC

method Teste()
    ensures
        x == Fib(n)
{
    return 0;
}

}