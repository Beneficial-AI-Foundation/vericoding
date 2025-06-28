use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat) -> bool
    requires valid_base(b)
{
    n < b
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

fn bibble_add(b: nat, p: Seq<nat>, q: Seq<nat>) -> (r: Seq<nat>)
    requires bibble(b, p) && bibble(b, q)
    ensures bibble(b, r)
{
    let mut carry = 0nat;
    let mut result = seq![0nat; 4];
    
    // Add digit by digit with carry
    let (z0, c0) = nit_add_three(b, carry, p[0], q[0]);
    result = result.update(0, z0);
    carry = c0;
    
    let (z1, c1) = nit_add_three(b, carry, p[1], q[1]);
    result = result.update(1, z1);
    carry = c1;
    
    let (z2, c2) = nit_add_three(b, carry, p[2], q[2]);
    result = result.update(2, z2);
    carry = c2;
    
    let (z3, _c3) = nit_add_three(b, carry, p[3], q[3]);
    result = result.update(3, z3);
    
    // Prove that the result satisfies bibble
    assert(result.len() == 4);
    assert(valid_base(b));
    assert(forall|i: int| 0 <= i < result.len() ==> nitness(b, result[i])) by {
        assert(nitness(b, result[0]));
        assert(nitness(b, result[1]));
        assert(nitness(b, result[2]));
        assert(nitness(b, result[3]));
    };
    
    result
}

fn nit_add(b: nat, x: nat, y: nat) -> (result: (nat, nat))
    requires valid_base(b) && nitness(b, x) && nitness(b, y)
    ensures nitness(b, result.0) && (result.1 == 0 || result.1 == 1)
{
    let sum = x + y;
    let z = sum % b;
    let carry = sum / b;
    
    assert(sum < 2 * b) by {
        assert(x < b);
        assert(y < b);
    };
    
    assert(carry < 2) by {
        assert(sum < 2 * b);
    };
    
    (z, carry)
}

fn max_nit(b: nat) -> (nmax: nat)
    requires valid_base(b)
    ensures nitness(b, nmax) && is_max_nit(b, nmax)
{
    let nmax = b - 1;
    assert(nmax < b) by {
        assert(b >= 2);
    };
    nmax
}

fn nit_flip(b: nat, n: nat) -> (nf: nat)
    requires valid_base(b) && nitness(b, n)
    ensures nitness(b, nf)
{
    let nf = (b - 1) - n;
    assert(nf < b) by {
        assert(n < b);
        assert(b >= 2);
        assert(nf <= b - 1);
    };
    nf
}

fn nit_add_three(b: nat, c: nat, x: nat, y: nat) -> (result: (nat, nat))
    requires valid_base(b) && (c == 0 || c == 1) && nitness(b, x) && nitness(b, y)
    ensures nitness(b, result.0) && (result.1 == 0 || result.1 == 1)
{
    let sum = c + x + y;
    let z = sum % b;
    let carry = sum / b;
    
    assert(sum < 2 * b) by {
        assert(c <= 1);
        assert(x < b);
        assert(y < b);
        assert(c + x + y <= 1 + (b - 1) + (b - 1));
        assert(c + x + y <= 2 * b - 1);
    };
    
    assert(carry < 2) by {
        assert(sum <= 2 * b - 1);
    };
    
    (z, carry)
}

fn bibble_increment(b: nat, p: Seq<nat>) -> (r: Seq<nat>)
    requires bibble(b, p)
    ensures bibble(b, r)
{
    let one_bibble = seq![1nat, 0nat, 0nat, 0nat];
    
    // Prove that one_bibble satisfies bibble
    assert(one_bibble.len() == 4);
    assert(valid_base(b)) by {
        assert(bibble(b, p));
    };
    assert(b >= 2);
    assert(1 < b) by {
        assert(b >= 2);
    };
    assert(0 < b) by {
        assert(b >= 2);
    };
    assert(forall|i: int| 0 <= i < one_bibble.len() ==> nitness(b, one_bibble[i])) by {
        assert(nitness(b, one_bibble[0]));
        assert(nitness(b, one_bibble[1]));
        assert(nitness(b, one_bibble[2]));
        assert(nitness(b, one_bibble[3]));
    };
    assert(bibble(b, one_bibble));
    
    bibble_add(b, p, one_bibble)
}

fn bibble_flip(b: nat, p: Seq<nat>) -> (fp: Seq<nat>)
    requires bibble(b, p)
    ensures bibble(b, fp)
{
    let fp = seq![
        nit_flip(b, p[0]),
        nit_flip(b, p[1]), 
        nit_flip(b, p[2]),
        nit_flip(b, p[3])
    ];
    
    assert(fp.len() == 4);
    assert(valid_base(b)) by {
        assert(bibble(b, p));
    };
    assert(forall|i: int| 0 <= i < fp.len() ==> nitness(b, fp[i])) by {
        assert(nitness(b, fp[0]));
        assert(nitness(b, fp[1]));
        assert(nitness(b, fp[2]));
        assert(nitness(b, fp[3]));
    };
    
    fp
}

fn n_complement(b: nat, p: Seq<nat>) -> (com: Seq<nat>)
    requires bibble(b, p)
    ensures bibble(b, com)
{
    let flipped = bibble_flip(b, p);
    let one_bibble = seq![1nat, 0nat, 0nat, 0nat];
    
    // Prove that one_bibble satisfies bibble
    assert(one_bibble.len() == 4);
    assert(valid_base(b)) by {
        assert(bibble(b, p));
    };
    assert(b >= 2);
    assert(1 < b) by {
        assert(b >= 2);
    };
    assert(0 < b) by {
        assert(b >= 2);
    };
    assert(forall|i: int| 0 <= i < one_bibble.len() ==> nitness(b, one_bibble[i])) by {
        assert(nitness(b, one_bibble[0]));
        assert(nitness(b, one_bibble[1]));
        assert(nitness(b, one_bibble[2]));
        assert(nitness(b, one_bibble[3]));
    };
    assert(bibble(b, one_bibble));
    
    bibble_add(b, flipped, one_bibble)
}

}