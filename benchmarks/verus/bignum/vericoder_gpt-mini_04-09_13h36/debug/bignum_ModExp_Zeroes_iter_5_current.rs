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
        0nat
    } else {
        let last_idx = s.len() - 1;
        let last = s[last_idx];
        let prefix = &s[..last_idx];
        let r = slice_to_nat(prefix);
        if last == '1' { (r * 2nat) + 1nat } else { r * 2nat }
    }
}

exec fn pow_full(base: nat, exp: nat) -> (result: nat)
  ensures result == Exp_int(base, exp)
  decreases exp
{
    if exp == 0nat {
        1nat
    } else {
        base * pow_full(base, exp - 1nat)
    }
}

exec fn nat_to_bits(n: nat) -> (result: Vec<char>)
  ensures ValidBitString(result@) && Str2Int(result@) == n
  decreases n
{
    if n == 0nat {
        Vec::<char>::new()
    } else {
        let mut v = nat_to_bits(n / 2nat);
        let b = if n % 2nat == 1nat { '1' } else { '0' };
        v.push(b);
        proof {
            // From recursive postcondition
            assert(Str2Int(v@) == n / 2nat);
            let seq_val = Str2Int(v@);
            if b == '1' {
                assert((seq_val * 2nat) + 1nat == n);
            } else {
                assert((seq_val * 2nat) + 0nat == n);
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
    let p = pow_full(x, y);
    let r = p % m;
    nat_to_bits(r)
}
// </vc-code>

fn main() {}
}