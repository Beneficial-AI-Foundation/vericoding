// Translated from Dafny
use builtin::*;
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

spec fn spec_max_nit(b: nat) -> nmax : nat
    requires
        (valid_base(b))
    ensures
        (nitness(b, nmax)),
        (is_max_nit(b, nmax))
;

proof fn lemma_max_nit(b: nat) -> (nmax: nat)
    requires
        (valid_base(b))
    ensures
        (nitness(b, nmax)),
        (is_max_nit(b, nmax))
{
    0
}

}