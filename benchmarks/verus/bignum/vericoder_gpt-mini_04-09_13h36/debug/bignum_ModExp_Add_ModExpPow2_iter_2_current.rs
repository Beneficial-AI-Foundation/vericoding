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
exec fn seq_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    let mut i: usize = 0;
    let mut acc: nat = 0;
    while i < s.len() {
        invariant i <= s.len();
        invariant acc == Str2Int(s@.subrange(0, i as int));
        decreases s.len() - i;
        let bit = s[i];
        if bit == '1' {
            acc = 2 * acc + 1;
        } else {
            // bit must be '0' due to ValidBitString
            acc = 2 * acc;
        }
        i = i + 1;
    }
    acc
}

exec fn full_exp(x: nat, y: nat) -> nat
  ensures result == Exp_int(x, y)
  decreases y
{
    if y == 0 {
        1
    } else {
        x * full_exp(x, y - 1)
    }
}

exec fn nat_to_seq(n: nat) -> Vec<char>
  ensures Str2Int(result@) == n && ValidBitString(result@)
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = nat_to_seq(q);
        if r == 1 {
            v.push('1');
        } else {
            v.push('0');
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = seq_to_nat(sx);
    let y = seq_to_nat(sy);
    let z = seq_to_nat(sz);
    let e = full_exp(x, y);
    let r = e % z;
    let res = nat_to_seq(r);
    return res;
}
// </vc-code>

fn main() {}
}