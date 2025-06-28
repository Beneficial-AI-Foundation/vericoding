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

fn max_nit(b: nat) -> (nmax: nat)
    requires valid_base(b)
    ensures nitness(b, nmax)
    ensures is_max_nit(b, nmax)
{
    let nmax = b - 1;
    nmax
}

fn bibble_flip(b: nat, p: Seq<nat>) -> (fp: Seq<nat>)
    requires valid_base(b)
    requires bibble(b, p)
    ensures bibble(b, fp)
{
    let n0 = nit_flip(b, p[0]);
    let n1 = nit_flip(b, p[1]);
    let n2 = nit_flip(b, p[2]);
    let n3 = nit_flip(b, p[3]);
    
    let fp = seq![n0, n1, n2, n3];
    
    assert(bibble(b, fp)) by {
        assert(valid_base(b));
        assert(fp.len() == 4);
        assert(nitness(b, n0));
        assert(nitness(b, n1));  
        assert(nitness(b, n2));
        assert(nitness(b, n3));
        assert(forall|i: int| 0 <= i < fp.len() ==> nitness(b, fp[i])) by {
            assert forall|i: int| 0 <= i < 4 implies nitness(b, fp[i]) by {
                if i == 0 {
                    assert(fp[i] == n0);
                    assert(nitness(b, n0));
                } else if i == 1 {
                    assert(fp[i] == n1);
                    assert(nitness(b, n1));
                } else if i == 2 {
                    assert(fp[i] == n2);
                    assert(nitness(b, n2));
                } else if i == 3 {
                    assert(fp[i] == n3);
                    assert(nitness(b, n3));
                }
            }
        }
    };
    
    fp
}

}