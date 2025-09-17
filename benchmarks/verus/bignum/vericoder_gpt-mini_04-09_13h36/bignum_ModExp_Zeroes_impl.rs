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
exec fn slice_to_nat(s: &[char]) -> (result: nat)
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_idx = s.len() - 1;
        let last = s[last_idx];
        let prefix = &s[..last_idx];
        let r = slice_to_nat(prefix);
        if last == '1' { (r * 2) + 1 } else { r * 2 }
    }
}

exec fn pow_full(base: nat, exp: nat) -> (result: nat)
  ensures result == Exp_int(base, exp)
  decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_full(base, exp - 1)
    }
}

exec fn nat_to_bits(n: nat) -> (result: Vec<char>)
  ensures ValidBitString(result@) && Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut v = nat_to_bits(n / 2);
        let seq_before = v@;
        let b = if n % 2 == 1 { '1' } else { '0' };
        v.push(b);
        proof {
            // From recursive postcondition on the vec before push
            assert(Str2Int(seq_before) == n / 2);
            let seq_val = Str2Int(seq_before);
            if b == '1' {
                assert((seq_val * 2) + 1 == n);
            } else {
                assert((seq_val * 2) + 0 == n);
            }
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = slice_to_nat(sx);
    let y = slice_to_nat(sy);
    let m = slice_to_nat(sz);
    proof {
        assert(x == Str2Int(sx@));
        assert(y == Str2Int(sy@));
        assert(m == Str2Int(sz@));
    }
    let p = pow_full(x, y);
    proof {
        assert(p == Exp_int(x, y));
    }
    let r = p % m;
    proof {
        assert(r == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    nat_to_bits(r)
}
// </vc-code>

fn main() {}
}