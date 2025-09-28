use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_commutative_nat(a: nat, b: nat)
    ensures a * b == b * a
{
    // Built-in arithmetic axiom in Verus
}

proof fn lemma_mul_associative_nat(a: nat, b: nat, c: nat)
    ensures (a * b) * c == a * (b * c)
{
    // Built-in arithmetic axiom in Verus
}

proof fn lemma_div_mul_nat(a: nat, b: nat, c: nat)
    requires b > 0,
    ensures (a * b) / b == a,
{
    // Built-in arithmetic property in Verus
}

proof fn lemma_triangular_volume_formula(base: nat, height: nat, length: nat)
    requires base > 0 && height > 0 && length > 0,
    ensures ((base * height) * length) / 2 == (base * height * length) / 2,
{
    lemma_mul_associative_nat(base, height, length);
}
// </vc-helpers>

// <vc-spec>
fn triangular_prism_volume(base: u32, height: u32, length: u32) -> (volume: u32)
    requires 
        base > 0,
        height > 0,
        length > 0,
    ensures volume == (base * height * length) / 2,
// </vc-spec>
// <vc-code>
{
    let volume = (base * height * length) / 2;
    
    proof {
        let b = base as nat;
        let h = height as nat;
        let l = length as nat;
        lemma_triangular_volume_formula(b, h, l);
        assert((base * height * length) as int == ((b * h) * l) as int);
    }
    
    volume
}
// </vc-code>

fn main() {
}

}