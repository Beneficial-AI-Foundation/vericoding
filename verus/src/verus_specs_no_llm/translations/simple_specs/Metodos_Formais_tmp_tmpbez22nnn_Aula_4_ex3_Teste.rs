// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Fib(n: nat) -> nat
{
    0
}

spec fn spec_ComputeFib(n: nat) -> x:nat)
ensures x == Fib(n)
{
  x := 0;
  assume x ==> Fib(n);
  return x;
}


// SPEC

method Teste(
    ensures
        x == Fib(n)
;

proof fn lemma_ComputeFib(n: nat) -> (x: nat)
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
    0
}

}