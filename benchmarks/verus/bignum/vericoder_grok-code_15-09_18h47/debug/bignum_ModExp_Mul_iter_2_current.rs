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

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type mismatches by using nat literals */
{
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let product = n1 * n2;
    let mut result = Vec::<char>::new();
    if product == 0nat {
        result.push('0');
    } else {
        let mut n = product;
        while n > 0nat
            invariant n > 0nat,
            decreases n
        {
            result.push(if n % 2nat == 1nat { '1' } else { '0' });
            n = n / 2nat;
        }
        result.reverse();
    }
    result
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type mismatches by using nat literals */
{
    let mod_value = Str2Int(sz@);
    let base_value = Str2Int(sx@) % mod_value;
    let exp_value = Str2Int(sy@);
    let mut result: nat = 1nat;
    let mut b: nat = base_value;
    let mut current_exp = exp_value;
    while current_exp > 0nat
        invariant current_exp >= 0nat,
        decreases current_exp
    {
        if current_exp % 2nat == 1nat {
            result = (result * b) % mod_value;
        }
        current_exp = current_exp / 2nat;
        b = (b * b) % mod_value;
    }
    let mut res_bits = Vec::<char>::new();
    if result == 0nat {
        res_bits.push('0');
    } else {
        let mut n = result;
        while n > 0nat
            invariant n > 0nat,
            decreases n
        {
            res_bits.push(if n % 2nat == 1nat { '1' } else { '0' });
            n = n / 2nat;
        }
        res_bits.reverse();
    }
    res_bits
}
// </vc-code>

fn main() {}
}
