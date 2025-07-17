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
spec fn requires(valid_base(b))
  requires (nitness(b, n))
  ensures (nitness(b, sum))
  ensures (nitness(b, carry)) -> bool {
    
}
spec fn is_max_nit(b: nat, q: nat) -> bool {
    q == b - 1
}
spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) && 
  a.len() == 4 && 
  forall |n: int| n in a ==> nitness(b, n)
}

spec fn spec_nit_increment(b: nat, n: nat) -> sum : nat, carry : nat)
  // Note: apparently, you need to explicitly put this here
  // even though we've got it in the nitness predicate
  requires (valid_base(b)
    requires
        (valid_base(b)),
        (nitness(b, n))
    ensures
        (nitness(b, sum)),
        (nitness(b, carry))
;

proof fn lemma_nit_increment(b: nat, n: nat) -> (sum: nat, carry: nat)
  // Note: apparently, you need to explicitly put this here
  // even though we've got it in the nitness predicate
  requires (valid_base(b))
    requires
        (valid_base(b)),
        (nitness(b, n))
    ensures
        (nitness(b, sum)),
        (nitness(b, carry))
{
    (0, 0, 0)
}

}