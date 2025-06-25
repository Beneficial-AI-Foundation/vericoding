// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn valid_base(b: nat) -> bool {
    b >= 2
}
spec fn nitness(b: nat, n: nat)
  requires (valid_base(b)) -> bool {
    0 <= n < b
}
spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) and 
  a.len() == 4 and 
  forall|n: int| n in a ==> nitness(b, n)
}
spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) and 
  a.len() == 4 and 
  forall|n: int| n in a ==> nitness(b, n)
}
spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) and 
  a.len() == 4 and 
  forall|n: int| n in a ==> nitness(b, n)
}

fn nit_add(b: nat, x: nat, y: nat) -> z: nat, carry: nat
    requires (valid_base(b)),
             (nitness(b, x)),
             (nitness(b, y))
    ensures (nitness(b, z)),
            (nitness(b, carry))
  // This is a useful fact for doing general form addition.,
            (carry == 0 or carry == 1)
{
}

}