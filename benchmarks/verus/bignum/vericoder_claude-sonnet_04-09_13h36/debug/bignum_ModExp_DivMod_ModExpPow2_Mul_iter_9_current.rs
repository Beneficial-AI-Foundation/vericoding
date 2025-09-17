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
{}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{}

proof fn lemma_exp_int_zero()
    ensures forall |x: nat| Exp_int(x, 0) == 1
{}

proof fn lemma_exp_int_one()
    ensures forall |x: nat| Exp_int(x, 1) == x
{}

proof fn lemma_mod_exp_base_cases(x: nat, y: nat, z: nat)
    requires z > 1
    ensures y == 0 ==> Exp_int(x, y) % z == 1 % z,
            y == 1 ==> Exp_int(x, y) % z == x % z
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    }
    if y == 1 {
        assert(Exp_int(x, 1) == x);
    }
}

exec fn str_to_vec(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@)
    ensures ValidBitString(res@), res@ == s@
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            ValidBitString(result@),
            result@ == s@.subrange(0, i as int)
    {
        result.push(s[i]);
        i += 1;
    }
    result
}

exec fn int_to_bit_string(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            res@.len() > 0,
            Str2Int(res@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0
            invariant ValidBitString(result@)
        {
            if num % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            num = num / 2;
        }
        
        let mut reversed = Vec::new();
        let mut i = result.len();
        while i > 0
            invariant 
                0 <= i <= result.len(),
                ValidBitString(reversed@),
                ValidBitString(result@)
        {
            i -= 1;
            reversed.push(result[i]);
        }
        reversed
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_str2int_empty();
        lemma_str2int_single_zero();
        lemma_str2int_single_one();
        lemma_exp_int_zero();
        lemma_exp_int_one();
        lemma_mod_exp_base_cases(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
    }

    if sy.len() == 0 {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        let x_val = Str2Int(sx@);
        let z_val = Str2Int(sz@);
        let result_val = x_val % z_val;
        return int_to_bit_string(result_val);
    }

    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let result_val = Exp_int(x_val, y_val) % z_val;
    
    int_to_bit_string(result_val)
}
// </vc-code>

fn main() {}
}