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
/* helper modified by LLM (iteration 3): Fix ghost code usage in exec context */
proof fn helper_lemma_exp_mod(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
{
    if y == 0 {
        assert(Exp_int(x, 0) % m == 1 % m) by {
            assert(1 % m == 1) by { assert(m > 1); }
        };
        assert(Exp_int(x % m, 0) % m == 1 % m) by {
            assert(1 % m == 1) by { assert(m > 1); }
        };
    } else {
        helper_lemma_exp_mod(x, (y - 1) as nat, m);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)) by { };
        assert(Exp_int(x % m, y) == (x % m) * Exp_int(x % m, (y - 1) as nat)) by { };
        assert((x * Exp_int(x, (y - 1) as nat)) % m == (x % m) * (Exp_int(x, (y - 1) as nat) % m) % m) by { };
        assert(Exp_int(x, (y - 1) as nat) % m == Exp_int(x % m, (y - 1) as nat) % m);
    }
}

proof fn helper_lemma_str2int_mod(s: Seq<char>, m: nat)
    requires ValidBitString(s), m > 1
    ensures Str2Int(s) % m == if s.len() == 0 { 0 } else { (2 * (Str2Int(s.subrange(0, s.len() as int - 1)) % m) + (if s[s.len() as int - 1] == '1' { 1 } else { 0 })) % m }
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0) by { };
        assert(0 % m == 0) by { };
    } else {
        let last_char_bit = if s[s.len() as int - 1] == '1' { 1 } else { 0 };
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + last_char_bit) by { };
        assert((2 * Str2Int(s.subrange(0, s.len() as int - 1)) + last_char_bit) % m == (2 * (Str2Int(s.subrange(0, s.len() as int - 1)) % m) + last_char_bit) % m) by { };
        helper_lemma_str2int_mod(s.subrange(0, s.len() as int - 1), m);
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
/* code modified by LLM (iteration 3): Remove ghost code from exec context and fix type conversions */
{
    proof {
        let m_val = Str2Int(sz@);
        let x_val = Str2Int(sx@);
        let x_mod_m = x_val % m_val;
        let y_val = Str2Int(sy@);
        helper_lemma_exp_mod(x_val, y_val, m_val);
    }
    
    let mut result: u64 = 1;
    let mut current_base: u64 = 0;
    let mut remaining_exp: u64 = 0;
    let m_int = sz.len() as u64;
    
    proof {
        current_base = (Str2Int(sx@) % Str2Int(sz@)) as u64;
        remaining_exp = Str2Int(sy@) as u64;
    }
    
    while remaining_exp > 0
        invariant
            remaining_exp >= 0,
            result as nat * Exp_int(current_base as nat, remaining_exp as nat) % Str2Int(sz@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@),
            current_base as nat == Exp_int(Str2Int(sx@) % Str2Int(sz@), Exp_int(2, (Str2Int(sy@) - remaining_exp as nat) as nat)) % Str2Int(sz@)
    {
        if remaining_exp % 2 == 1 {
            result = (result * current_base) % m_int;
        }
        current_base = (current_base * current_base) % m_int;
        remaining_exp = remaining_exp / 2;
    }
    
    let mut res_vec = Vec::new();
    let mut num = result;
    
    while num > 0
        invariant
            num >= 0,
            Str2Int(res_vec@) == result - num * Exp_int(2, res_vec@.len() as nat)
    {
        let bit = if num % 2 == 1 { '1' } else { '0' };
        res_vec.push(bit);
        num = num / 2;
    }
    
    res_vec.reverse();
    
    if res_vec.is_empty() {
        res_vec.push('0');
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
