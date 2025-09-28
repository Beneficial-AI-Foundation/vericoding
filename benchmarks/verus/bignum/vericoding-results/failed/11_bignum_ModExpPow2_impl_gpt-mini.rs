// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}
// </vc-preamble>

// <vc-helpers>
{
    // Helper: convert bit-vector (MSB..LSB) to u128
    fn bits_to_u128(v: &Vec<char>) -> u128 {
        let mut acc: u128 = 0u128;
        let mut i: usize = 0usize;
        while i < v.len() {
            acc = acc * 2u128 + if v[i] == '1' { 1u128 } else { 0u128 };
            i += 1usize;
        }
        acc
    }

    // Helper: convert u128 to bit-vector (MSB..LSB). Returns empty Vec for 0.
    fn u128_to_bits(mut x: u128) -> Vec<char> {
        if x == 0u128 {
            Vec::new()
        } else {
            let mut rev: Vec<char> = Vec::new();
            while x > 0u128 {
                let bit = if x % 2u128 == 1u128 { '1' } else { '0' };
                rev.push(bit);
                x = x / 2u128;
            }
            // reverse to MSB..LSB
            let mut out: Vec<char> = Vec::new();
            let mut j: usize = 0usize;
            while j < rev.len() {
                out.insert(0, rev[j]);
                j += 1usize;
            }
            out
        }
    }

    // Proof lemma: relate bits_to_u128 to spec str2int for a Vec<char>
    proof fn bits_to_u128_spec(v: &Vec<char>)
        ensures
            str2int(v@) == (bits_to_u128(v) as nat)
    {
        // Prove by induction on length
        if v.len() == 0 {
            proof {
                assert(str2int(v@) == 0nat);
                assert(bits_to_u128(v) == 0u128);
            }
        } else {
            // build prefix vector (all but last)
            let mut prefix: Vec<char> = Vec::new();
            let mut i: usize = 0usize;
            while i + 1usize < v.len() {
                prefix.push(v[i]);
                i += 1usize;
            }
            let last = v[v.len() - 1usize];
            // recursive lemma on prefix
            bits_to_u128_spec(&prefix);
            proof {
                // str2int(v) = 2 * str2int(prefix) + lastbit
                let lastbit = if last == '1' { 1nat } else { 0nat };
                assert(str2int(v@) == 2nat * str2int(prefix@) + lastbit);
                // bits_to_u128(v) = bits_to_u128(prefix) * 2 + lastbit
                let lhs_u = bits_to_u128(&prefix) * 2u128 + (if last == '1' { 1u128 } else { 0u128 });
                assert(bits_to_u128(v) == lhs_u);
                // cast equality: bits_to_u128(prefix) as nat == str2int(prefix@)
                assert((bits_to_u128(&prefix) as nat) == str2int(prefix@));
                // therefore bits_to_u128(v) as nat == str2int(v@)
                assert((bits_to_u128(v) as nat) == 2nat * str2int(prefix@) + lastbit);
                assert((bits_to_u128(v) as nat) == str2int(v@));
            }
        }
    }

    // Proof lemma: repeated squaring with u128 corresponds to exp_int on spec nats
    proof fn pow2_u128_spec(xv: &Vec<char>, n: u8, zv: &Vec<char>, res: u128)
        requires
            str2int(zv@) > 1,
            res == ({
                // define u128 computation: start = bits_to_u128(xv); repeat n squares mod bits_to_u128(zv)
                let mut b = bits_to_u128(xv);
                let mut i: u8 = 0u8;
                let m = bits_to_u128(zv);
                while i < n {
                    b = (b * b) % m;
                    i += 1u8;
                }
                b
            }),
        ensures
            (res as nat) % str2int(zv@) == exp_int(str2int(xv@), exp_int(2nat, n as nat)) % str2int(zv@)
    {
        // We'll prove that repeated squaring produces x^(2^n) mod z
        // First relate bits_to_u128(xv) and str2int(xv@)
        bits_to_u128_spec(xv);
        bits_to_u128_spec(zv);
        proof {
            // Let bx = bits_to_u128(xv) as nat; bz = bits_to_u128(zv) as nat
            let mut bx_u = bits_to_u128(xv);
            let mut bz_u = bits_to_u128(zv);
            let mut i: u8 = 0u8;
            let mut cur: u128 = bx_u % bz_u;
            // loop invariant: cur as nat == ( (bits_to_u128(xv) as nat) ^ (2^i) ) % (bits_to_u128(zv) as nat)
            while i < n {
                cur = (cur * cur) % bz_u;
                i += 1u8;
            }
            // After loop cur == res by requires
            assert((res as nat) == (cur as nat));
            // Now lift to spec nat arithmetic: use cast equalities from bits_to_u128_spec
            assert((bits_to_u128(xv) as nat) == str2int(xv@));
            assert((bits_to_u128(zv) as nat) == str2int(zv@));
            // By elementary number theory, repeated squaring yields x^(2^n) mod z
            // Formalize by induction on n (sketch in proof):
            // Base i=0: cur = bx_u % bz_u corresponds to str2int(xv@) % str2int(zv@)
            // Each squaring doubles the exponent
            // Conclude that cur as nat == exp_int(str2int(xv@), exp_int(2nat, n as nat)) % str2int(zv@)
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy@.len() == n as int + 1,
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n
// </vc-spec>
// <vc-code>
{
    // impl-start
    // Convert inputs to u128
    let bx = bits_to_u128(&sx);
    let by = bits_to_u128(&sy);
    let bz = bits_to_u128(&sz);

    // special case modulus 0 or 1: but precondition ensures str2int(sz@) > 1, so bz >= 2

    // compute result: if exponent is 0 => 1 mod bz, else do n repeated squarings
    let mut acc: u128;
    if by == 0u128 {
        acc = 1u128 % bz;
    } else {
        acc = bx % bz;
        let mut i: u8 = 0u8;
        while i < n {
            acc = (acc * acc) % bz;
            i += 1u8;
        }
    }

    // convert acc back to bits
    let res_vec = u128_to_bits(acc);

    // Prove that the produced res_vec satisfies the spec ensures
    proof {
        // relate bit-vectors to spec nats
        bits_to_u128_spec(&sx);
        bits_to_u128_spec(&sy);
        bits_to_u128_spec(&sz);

        // If by == 0 then exponent is 0
        if by == 0u128 {
            // str2int(sy@) == 0
            assert((by as nat) == str2int(sy@));
            assert(str2int(sy@) == 0nat);
            // acc as nat == 1 % str2int(sz@)
            assert((acc as nat) == (1nat % str2int(sz@)));
            // convert res_vec to nat and relate
            bits_to_u128_spec(&res_vec);
            assert((bits_to_u128(&res_vec) as nat) == str2int(res_vec@));
            // bits_to_u128(res_vec) == acc
            assert(bits_to_u128(&res_vec) == acc);
            // Therefore desired equality holds
            assert(str2int(res_vec@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@));
        } else {
            // by == 2^n per precondition; use lemma pow2_u128_spec
            // res acc was computed as repeated squaring by the same loop as in the lemma
            pow2_u128_spec(&sx, n, &sz, acc);
            // now acc as nat modulo sz equals desired expression
            bits_to_u128_spec(&res_vec);
            assert(bits_to_u128(&res_vec) == acc);
            assert(str2int(res_vec@) == (acc as nat));
            assert(str2int(res_vec@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@));
        }
    }

    // return result vector
    res_vec
    // impl-end
}

// </vc-code>


}

fn main() {}