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
    assert(nitness(b, nf)) by {
        assert(b >= 2);
        assert(0 <= n < b);
        assert(n <= b - 1);
        assert(b - 1 >= n);
        assert(nf == (b - 1) - n);
        assert(nf >= 0);
        assert(nf <= b - 1);
        assert(nf < b);
        assert(0 <= nf < b);
    };
    nf
}

fn max_nit(b: nat) -> (nmax: nat)
    requires valid_base(b)
    ensures nitness(b, nmax)
    ensures is_max_nit(b, nmax)
{
    let nmax = b - 1;
    assert(nitness(b, nmax)) by {
        assert(b >= 2);
        assert(nmax == b - 1);
        assert(nmax >= 1);
        assert(nmax < b);
        assert(0 <= nmax);
        assert(0 <= nmax < b);
    };
    assert(is_max_nit(b, nmax)) by {
        assert(nmax == b - 1);
    };
    nmax
}

fn bibble_flip(b: nat, p: Seq<nat>) -> (fp: Seq<nat>)
    requires valid_base(b)
    requires bibble(b, p)
    ensures bibble(b, fp)
{
    assert(p.len() == 4);
    assert(forall|i: int| 0 <= i < p.len() ==> nitness(b, p[i]));
    assert(nitness(b, p[0]));
    assert(nitness(b, p[1]));
    assert(nitness(b, p[2]));
    assert(nitness(b, p[3]));
    
    let n0 = nit_flip(b, p[0]);
    let n1 = nit_flip(b, p[1]);
    let n2 = nit_flip(b, p[2]);
    let n3 = nit_flip(b, p[3]);
    
    let fp = seq![n0, n1, n2, n3];
    
    assert(bibble(b, fp)) by {
        assert(valid_base(b));
        assert(fp.len() == 4);
        assert(fp[0] == n0);
        assert(fp[1] == n1);
        assert(fp[2] == n2);
        assert(fp[3] == n3);
        assert(nitness(b, n0));
        assert(nitness(b, n1));  
        assert(nitness(b, n2));
        assert(nitness(b, n3));
        assert(forall|i: int| 0 <= i < fp.len() ==> nitness(b, fp[i])) by {
            assert(forall|i: int| 0 <= i < 4 ==> nitness(b, fp[i])) by {
                assert(nitness(b, fp[0]));
                assert(nitness(b, fp[1]));  
                assert(nitness(b, fp[2]));
                assert(nitness(b, fp[3]));
            };
        };
    };
    
    fp
}

}