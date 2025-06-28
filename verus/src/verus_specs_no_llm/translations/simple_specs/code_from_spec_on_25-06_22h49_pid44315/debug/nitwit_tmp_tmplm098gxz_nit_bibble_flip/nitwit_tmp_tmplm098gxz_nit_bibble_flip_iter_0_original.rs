// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat)
 requires (valid_base(b)) -> bool {
    0 <= n < b
}
spec fn valid_base(b: nat) -> bool {
    b >= 2
}
spec fn is_max_nit(b: nat, q: nat) -> bool {
    q == b - 1
}
spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) && 
 a.len() == 4 && 
 forall n :: n in a ==> nitness(b, n)
}

fn nit_flip(b: nat, n: nat) -> (nf: nat)
 requires (valid_base(b))
 requires (nitness(b, n))
 ensures (nitness (b, nf))
{
  nf: = 0;
  assume (nitness (b, nf));
  return nf;
}

/*
 We will now take a detour back to addition. We want to define
 a general version of nit_increment that allows you to add any two nits
*/


//ATOM
method max_nit(b: nat) returns (nmax : nat)
 requires (valid_base(b))
 ensures (nitness(b, nmax))
 ensures (is_max_nit(b, nmax))
{
  nmax: = 0;
  assume (nitness(b, nmax));
  assume (is_max_nit(b, nmax));
  return nmax;
}

/*
 Now we define the flip operation proper. For this to work, we need is_max_nit and a kind of silly proof to make Dafny
 happy.
*/


//ATOM
predicate bibble(b: nat, a: Seq<nat>, n)
}

/*
 As with nits, we will define addition, increment, and flip operations.
*/


// SPEC

method bibble_flip(b: nat, p: Seq<nat>) returns (fp : seq<nat>)
    requires
        (valid_base(b)),
        (nitness(b, n)),
        (valid_base(b)),
        (valid_base(b)),
        (bibble(b, p))
    ensures
        (nitness (b, nf)),
        (nitness(b, nmax)),
        (is_max_nit(b, nmax)),
        (bibble(b, fp))
{
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, Seq::empty(), 0, 0, 0, 0, Seq::empty());
}

}