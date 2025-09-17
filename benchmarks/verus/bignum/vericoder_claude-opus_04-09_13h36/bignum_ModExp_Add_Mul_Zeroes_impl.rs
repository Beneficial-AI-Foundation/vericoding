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

spec fn reverse_seq(s: Seq<char>) -> Seq<char>
{
    Seq::new(s.len(), |i: int| s[s.len() - 1 - i])
}

exec fn Int2Str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
    if n == 0 {
        proof { lemma_str2int_single_zero(); }
        return vec!['0'];
    }
    
    let mut reversed_result = Vec::<char>::new();
    let mut num = n;
    
    while num > 0
        invariant
            num <= n,
            ValidBitString(reversed_result@),
            num > 0 ==> reversed_result@.len() < 64,
    {
        if num % 2 == 1 {
            reversed_result.push('1');
        } else {
            reversed_result.push('0');
        }
        num = num / 2;
    }
    
    // Manually reverse the vector
    let mut result = Vec::<char>::new();
    let mut i = reversed_result.len();
    while i > 0
        invariant
            0 <= i <= reversed_result.len(),
            result@.len() == reversed_result.len() - i,
            ValidBitString(result@),
            ValidBitString(reversed_result@),
            forall |j: int| 0 <= j && j < result@.len() ==> result@[j] == reversed_result@[reversed_result@.len() - 1 - j],
    {
        i = i - 1;
        result.push(reversed_result[i]);
    }
    
    return result;
}

exec fn ModMul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), Str2Int(sz@) > 0
    ensures ValidBitString(res@), Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@)
{
    let x_val = Str2IntExec(sx);
    let y_val = Str2IntExec(sy);
    let z_val = Str2IntExec(sz);
    
    let product = (x_val * y_val) % z_val;
    return Int2Str(product);
}

exec fn Str2IntExec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res as nat == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        return 0;
    }
    
    let mut result = 0u64;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result as nat == Str2Int(s@.subrange(0, i as int)),
    {
        result = 2 * result;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    return result;
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
    
    let mut sy_prefix = Vec::<char>::new();
    let mut i: usize = 0;
    while i < sy.len() - 1
        invariant
            0 <= i <= sy.len() - 1,
            sy_prefix@.len() == i,
            forall |j: int| 0 <= j && j < i ==> sy_prefix@[j] == sy@[j],
            ValidBitString(sy_prefix@),
    {
        sy_prefix.push(sy[i]);
        i = i + 1;
    }
    
    let last_bit = sy[sy.len() - 1];
    
    let recursive_result = ModExp_Add_Mul_Zeroes(&sy_prefix, sy, sz);
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