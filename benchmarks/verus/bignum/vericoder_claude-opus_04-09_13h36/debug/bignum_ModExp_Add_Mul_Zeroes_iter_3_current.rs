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
proof fn lemma_exp_int_base(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_int_recursive(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_str2int_empty()
    ensures Str2Int(seq![]) == 0
{
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
}

exec fn Int2Str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        proof { lemma_str2int_single_zero(); }
        return vec!['0'];
    }
    
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    while num > 0
        invariant
            num <= n,
            ValidBitString(result@),
            n == num * Exp_int(2, result@.len() as nat) + Str2Int(result@),
            num > 0 ==> result@.len() < 64,
    {
        if num % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        num = num / 2;
    }
    
    result.reverse();
    return result;
}

exec fn ModMul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), Str2Int(sz@) > 0
    ensures ValidBitString(res@), Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@)
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let product = (x_val * y_val) % z_val;
    return Int2Str(product);
}

exec fn Str2IntExec(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        return 0;
    }
    
    let prefix = &s[..s.len() - 1];
    let last_char = s[s.len() - 1];
    
    let prefix_val = Str2IntExec(prefix);
    
    if last_char == '1' {
        return 2 * prefix_val + 1;
    } else {
        return 2 * prefix_val;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 1 {
        if sy[0] == '0' {
            proof { 
                lemma_exp_int_base(Str2Int(sx@));
                lemma_str2int_single_one();
            }
            return vec!['1'];
        } else {
            // sy[0] == '1', so Str2Int(sy@) == 1
            // Exp_int(x, 1) = x
            let x_val = Str2IntExec(sx);
            let z_val = Str2IntExec(sz);
            let result_val = x_val % z_val;
            return Int2Str(result_val);
        }
    }
    
    let sy_prefix = &sy[..sy.len() - 1];
    let last_bit = sy[sy.len() - 1];
    
    let recursive_result = ModExp_Add_Mul_Zeroes(sx, sy_prefix, sz);
    let squared = ModMul(&recursive_result, &recursive_result, sz);
    
    if last_bit == '1' {
        return ModMul(&squared, sx, sz);
    } else {
        return squared;
    }
}
// </vc-code>

fn main() {}
}