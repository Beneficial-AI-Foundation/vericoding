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
exec fn bits_to_nat(s: &[char]) -> nat
  ensures Str2Int(s@) == result
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last = s[s.len() - 1];
        let prefix = &s[..s.len() - 1];
        let v = bits_to_nat(prefix);
        let bit = if last == '1' { 1 } else { 0 };
        2 * v + bit
    }
}

exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures Str2Int(result@) == n
  ensures ValidBitString(result@)
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut prefix = nat_to_bits(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        prefix.push(c);
        prefix
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = bits_to_nat(sx);
    let y = bits_to_nat(sy);
    let z = bits_to_nat(sz);

    // compute pow = Exp_int(x, y) % z by repeated multiplication
    let mut pow: nat = 1 % z;
    let mut processed: nat = 0;
    let mut remaining: nat = y;
    while remaining > 0
        invariant processed + remaining == y
        invariant pow == Exp_int(x, processed) % z
        decreases remaining
    {
        pow = (pow * x) % z;
        processed = processed + 1;
        remaining = remaining - 1;
    }

    let res = nat_to_bits(pow);
    res
}
// </vc-code>

fn main() {}
}