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
spec fn requires(valid_base(b))
  requires (nitness(b, n))
  ensures (nitness(b, sum))
  ensures (nitness(b, carry)) -> bool {
    
}

fn nit_increment(b: nat, n: nat) -> (sum: nat, carry: nat)
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
    return (0, 0, 0);
}

}