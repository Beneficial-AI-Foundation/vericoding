use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
decreases y
{
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
    forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
exec fn pow_mod(x: nat, y: nat, m: nat) -> (result: nat)
  requires m > 0
  ensures result == Exp_int(x, y) % m
  decreases y
{
    if y == 0 {
        let r = 1 % m;
        proof {
            assert(Exp_int(x, 0) == 1);
            assert(r == Exp_int(x, 0) % m);
        }
        return r;
    } else {
        if y % 2 == 0 {
            let t = pow_mod(x, y / 2, m);
            let res = (t * t) % m;
            proof {
                // induction hypothesis
                assert(t == Exp_int(x, y / 2) % m);
                // Use algebra of modular arithmetic and exponentiation:
                assert(res == (Exp_int(x, y / 2) % m) * (Exp_int(x, y / 2) % m) % m);
                assert(res == (Exp_int(x, y / 2) * Exp_int(x, y / 2)) % m);
                assert(res == Exp_int(x, y) % m);
            }
            return res;
        } else {
            let t = pow_mod(x, y - 1, m);
            let res = (x * t) % m;
            proof {
                assert(t == Exp_int(x, y - 1) % m);
                assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
                assert(res == (x % m) * (Exp_int(x, y - 1) % m) % m);
                assert(res == (x * Exp_int(x, y - 1)) % m);
                assert(res == Exp_int(x, y) % m);
            }
            return res;
        }
    }
}

exec fn nat_to_bits(n: nat) -> (v: Vec<char>)
  ensures ValidBitString(v@) && Str2Int(v@) == n
  decreases n
{
    if n == 0 {
        return Vec::<char>::new();
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = nat_to_bits(q);
        // capture the prefix sequence before push
        let seq_before: Seq<char> = v@;
        proof {
            assert(Str2Int(seq_before) == q);
        }
        if r == 1 {
            v.push('1');
        } else {
            v.push('0');
        }
        proof {
            // after push, the previous sequence is the prefix of the new sequence
            let len_before = seq_before.len();
            // v@.len() == len_before + 1 holds by Vec semantics
            assert(v@.subrange(0, len_before as int) == seq_before);
            // last bit equals what we pushed
            assert(v@[v@.len() - 1] == (if r == 1 { '1' } else { '0' }));
            // by definition of Str2Int for non-empty sequences:
            // Str2Int(v@) == 2 * Str2Int(prefix) + last_bit
            assert(Str2Int(v@) == 2 * Str2Int(v@.subrange(0, v@.len() - 1)) + (if v@[v@.len() - 1] == '1' { 1 } else { 0 }));
            // substitute prefix and last bit values
            assert(Str2Int(v@) == 2 * q + r);
            assert(Str2Int(v@) == n);
            // ValidBitString follows from induction and the fact we pushed '0' or '1'
            assert(ValidBitString(v@));
        }
        return v;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // convert inputs to nats
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let m = Str2Int(sz@);

    // compute modular exponentiation
    let r = pow_mod(x, y, m);

    // convert result to bitstring Vec<char>
    let res_vec = nat_to_bits(r);

    // final proof obligations are satisfied by helper ensures
    return res_vec;
}
// </vc-code>

fn main() {}
}