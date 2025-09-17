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
fn mul_impl(s1: &[char], s2: &[char]) -> Vec<char>
    requires ValidBitString(s1@), ValidBitString(s2@)
    ensures ValidBitString(ret@), Str2Int(ret@) == Str2Int(s1@) * Str2Int(s2@)
{
    let x = Str2Int(s1@);
    let y = Str2Int(s2@);
    let product = x * y;
    proof {
        assert(product == Str2Int(s1@) * Str2Int(s2@));
    }
    let mut result = Vec::new();
    let n = product;
    if n == 0 {
        result.push('0');
    } else {
        let mut temp = n;
        while temp > 0
            invariant
                ValidBitString(result@),
                temp >= 0,
                n == Str2Int(result@) + temp * Exp_int(2, result@.len() as nat)
            decreases temp
        {
            if temp % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            temp = temp / 2;
        }
        result.reverse();
    }
    result
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    
    proof {
        assert(y == Exp_int(2, n as nat) || y == 0);
    }
    
    if y == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let base = x % z;
    let mut result = base;
    let mut exp = n;
    
    while exp > 0
        invariant
            exp >= 0,
            result == Exp_int(base, Exp_int(2, (n - exp) as nat)) % z
        decreases exp
    {
        result = (result * result) % z;
        exp = exp - 1;
    }
    
    proof {
        assert(result == Exp_int(x, y) % z);
    }
    
    let mut binary_result = Vec::new();
    let n_val = result;
    if n_val == 0 {
        binary_result.push('0');
    } else {
        let mut temp = n_val;
        while temp > 0
            invariant
                ValidBitString(binary_result@),
                temp >= 0,
                n_val == Str2Int(binary_result@) + temp * Exp_int(2, binary_result@.len() as nat)
            decreases temp
        {
            if temp % 2 == 0 {
                binary_result.push('0');
            } else {
                binary_result.push('1');
            }
            temp = temp / 2;
        }
        binary_result.reverse();
    }
    binary_result
}
// </vc-code>

fn main() {}
}


