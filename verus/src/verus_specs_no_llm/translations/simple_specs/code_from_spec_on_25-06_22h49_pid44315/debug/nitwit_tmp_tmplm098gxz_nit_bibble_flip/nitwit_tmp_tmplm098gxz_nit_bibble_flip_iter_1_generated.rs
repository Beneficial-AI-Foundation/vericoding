use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat) -> bool 
    requires valid_base(b)
{
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
    forall|i: int| 0 <= i < a.len() ==> nitness(b, a[i])
}

fn nit_flip(b: nat, n: nat) -> (nf: nat)
    requires valid_base(b)
    requires nitness(b, n)
    ensures nitness(b, nf)
{
    let nf = (b - 1) - n;
    nf
}

method max_nit(b: nat) returns (nmax: nat)
    requires valid_base(b)
    ensures nitness(b, nmax)
    ensures is_max_nit(b, nmax)
{
    nmax = b - 1;
}

method bibble_flip(b: nat, p: Seq<nat>) returns (fp: Seq<nat>)
    requires valid_base(b)
    requires bibble(b, p)
    ensures bibble(b, fp)
{
    let n0 = nit_flip(b, p[0]);
    let n1 = nit_flip(b, p[1]);
    let n2 = nit_flip(b, p[2]);
    let n3 = nit_flip(b, p[3]);
    
    fp = seq![n0, n1, n2, n3];
}

}