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

spec fn valid_base(b: nat) -> bool {
    b >= 2
}
spec fn nitness(b: nat, n: nat)
  requires (valid_base(b)) -> bool {
    0 <= n < b
}
spec fn is_max_nit(b: nat, q: nat) -> bool {
    q == b - 1
}
spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) && 
  a.len() == 4 && 
  forall n :: n in a ==> nitness(b, n)
}

fn max_nit(b: nat) -> (nmax: nat)
    requires
        (valid_base(b))
    ensures
        (nitness(b, nmax)),
        (is_max_nit(b, nmax))
{
    return 0;
}

}