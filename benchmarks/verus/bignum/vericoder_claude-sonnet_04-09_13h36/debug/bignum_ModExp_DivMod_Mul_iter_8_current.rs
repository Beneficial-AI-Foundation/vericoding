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
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_one(x: nat)
    ensures Exp_int(x, 1) == x
{
}

proof fn lemma_mod_identity(x: nat, m: nat)
    requires m > 1
    ensures x % m < m
{
}

spec fn Int2Str_helper(n: nat, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0 {
        if acc.len() == 0 { seq!['0'] } else { acc }
    } else {
        Int2Str_helper(n / 2, seq![if n % 2 == 1 { '1' } else { '0' }] + acc)
    }
}

spec fn Int2Str(n: nat) -> Seq<char> {
    Int2Str_helper(n, Seq::<char>::empty())
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    lemma_int2str_helper_valid(n, Seq::<char>::empty());
}

proof fn lemma_int2str_helper_valid(n: nat, acc: Seq<char>)
    requires ValidBitString(acc)
    ensures ValidBitString(Int2Str_helper(n, acc))
    decreases n
{
    if n == 0 {
        if acc.len() == 0 {
            assert(ValidBitString(seq!['0']));
        }
    } else {
        let new_acc = seq![if n % 2 == 1 { '1' } else { '0' }] + acc;
        assert(ValidBitString(new_acc));
        lemma_int2str_helper_valid(n / 2, new_acc);
    }
}

exec fn int_to_bitvec(n: u32) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        result
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        
        while temp > 0
            invariant ValidBitString(result@)
            decreases temp
        {
            if temp % 2 == 1 {
                result.insert(0, '1');
            } else {
                result.insert(0, '0');
            }
            temp = temp / 2;
        }
        
        result
    }
}

exec fn bitvec_to_nat(bits: &[char]) -> (res: u32)
    requires ValidBitString(bits@)
    ensures res as nat == Str2Int(bits@)
{
    let mut result: u32 = 0;
    let mut i = 0;
    while i < bits.len()
        invariant 0 <= i <= bits.len()
        decreases bits.len() - i
    {
        result = result * 2;
        if bits[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}

exec fn mod_exp(base: u32, exp: u32, modulus: u32) -> (res: u32)
    requires modulus > 1
    ensures res as nat == Exp_int(base as nat, exp as nat) % modulus as nat
{
    if exp == 0 {
        1
    } else {
        let mut result: u32 = 1;
        let mut base_pow = base % modulus;
        let mut exp_remaining = exp;
        
        while exp_remaining > 0
            invariant modulus > 1,
                     result as nat * Exp_int(base_pow as nat, exp_remaining as nat) % modulus as nat == Exp_int(base as nat, exp as nat) % modulus as nat
            decreases exp_remaining
        {
            if exp_remaining % 2 == 1 {
                result = (result * base_pow) % modulus;
            }
            base_pow = (base_pow * base_pow) % modulus;
            exp_remaining = exp_remaining / 2;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = bitvec_to_nat(sx);
    let y_val = bitvec_to_nat(sy);
    let z_val = bitvec_to_nat(sz);
    
    if y_val == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let result_val = mod_exp(x_val, y_val, z_val);
    let result = int_to_bitvec(result_val);
    
    result
}
// </vc-code>

fn main() {}
}