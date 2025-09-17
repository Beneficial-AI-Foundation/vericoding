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
exec fn bits_to_nat(s: &[char]) -> (res: nat)
  requires ValidBitString(s@)
  ensures res == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        let res: nat = 0nat;
        proof {
            assert(res == Str2Int(s@));
        }
        return res;
    } else {
        let last = s.len() - 1;
        let prefix_slice = &s[..last];
        let prefix_seq: Seq<char> = prefix_slice@;
        // show the prefix slice is a valid bit string
        proof {
            // prefix_seq corresponds to the sequence subrange of s@
            assert(prefix_seq == s@.subrange(0, s@.len() as int - 1));
            // from ValidBitString(s@) derive ValidBitString(prefix_seq)
            assert(ValidBitString(s@));
            assert(forall |i: int|
                0 <= i && i < prefix_seq.len() as int ==>
                    (prefix_seq.index(i) == '0' || prefix_seq.index(i) == '1')
            );
        }
        let prefix = bits_to_nat(prefix_slice);
        let ch = s[last];
        let res: nat = if ch == '1' { 2nat * prefix + 1nat } else { 2nat * prefix };
        proof {
            // prefix corresponds to the integer value of the prefix slice
            assert(prefix == Str2Int(prefix_seq));
            // By definition of Str2Int for non-empty sequence:
            if ch == '1' {
                assert(res == 2nat * prefix + 1nat);
                assert(res == Str2Int(s@));
            } else {
                assert(res == 2nat * prefix);
                assert(res == Str2Int(s@));
            }
        }
        return res;
    }
}

exec fn pow_full(base: nat, exp: nat) -> (r: nat)
  ensures r == Exp_int(base, exp)
  decreases exp
{
    if exp == 0nat {
        let r: nat = 1nat;
        proof { assert(r == Exp_int(base, exp)); }
        return r;
    } else {
        let t = pow_full(base, exp - 1nat);
        let r: nat = base * t;
        proof {
            assert(t == Exp_int(base, exp - 1nat));
            assert(r == base * t);
            assert(r == Exp_int(base, exp));
        }
        return r;
    }
}

exec fn nat_to_bits(n: nat) -> (v: Vec<char>)
  ensures (Str2Int(v@) == n && ValidBitString(v@))
  decreases n
{
    if n == 0nat {
        let v0 = Vec::<char>::new();
        proof {
            assert(Str2Int(v0@) == 0nat);
            assert(ValidBitString(v0@));
        }
        return v0;
    } else {
        let mut prev = nat_to_bits(n / 2nat);
        let prev_before = prev@;
        // determine bit to push
        let ch = if n % 2nat == 1nat { '1' } else { '0' };
        prev.push(ch);
        let res = prev;
        proof {
            // res@ is prev_before extended by ch
            assert(res@.subrange(0, res@.len() as int - 1) == prev_before);
            // By recursive ensure
            assert(Str2Int(prev_before) == n / 2nat);
            // ch is either '0' or '1'
            if ch == '1' {
                assert(Str2Int(res@) == 2nat * Str2Int(prev_before) + 1nat);
            } else {
                assert(Str2Int(res@) == 2nat * Str2Int(prev_before));
            }
            // arithmetic: n == 2*(n/2) + (n%2)
            if n % 2nat == 1nat {
                assert(n == 2nat * (n / 2nat) + 1nat);
            } else {
                assert(n == 2nat * (n / 2nat));
            }
            assert(Str2Int(res@) == n);
            // ValidBitString preserved by push: prev_before valid and ch is bit
            assert(ValidBitString(prev_before));
            assert(ch == '0' || ch == '1');
            assert(ValidBitString(res@));
        }
        return res;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x: nat = bits_to_nat(sx);
    let y: nat = bits_to_nat(sy);
    let m: nat = bits_to_nat(sz);

    let full: nat = pow_full(x, y);
    let res_nat: nat = full % m;
    let res_vec: Vec<char> = nat_to_bits(res_nat);

    proof {
        assert(x == Str2Int(sx@));
        assert(y == Str2Int(sy@));
        assert(m == Str2Int(sz@));
        assert(full == Exp_int(x, y));
        assert(res_nat == full % m);
        assert(Str2Int(res_vec@) == res_nat);

        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == Exp_int(x, y));
        assert(Exp_int(x, y) == full);
        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == full);

        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) == full % m);
        assert(full % m == res_nat);
        assert(Str2Int(res_vec@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    return res_vec;
}
// </vc-code>

fn main() {}
}