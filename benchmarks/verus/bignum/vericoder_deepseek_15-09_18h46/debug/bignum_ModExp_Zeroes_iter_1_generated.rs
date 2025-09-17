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
        helper_lemma_exp_mod(x, y - 1, m);
        assert(Exp_int(x, y) == x * Exp_int(x, y - 1)) by { };
        assert(Exp_int(x % m, y) == (x % m) * Exp_int(x % m, y - 1)) by { };
        assert((x * Exp_int(x, y - 1)) % m == (x % m) * (Exp_int(x, y - 1) % m) % m) by { };
        assert(Exp_int(x, y - 1) % m == Exp_int(x % m, y - 1) % m);
    }
}

proof fn helper_lemma_str2int_mod(s: Seq<char>, m: nat)
    requires ValidBitString(s), m > 1
    ensures Str2Int(s) % m == Str2Int(Seq::new()) % m || (Str2Int(s.subrange(0, s.len() as int - 1)) * 2 + (if s[s.len() as int - 1] == '1' { 1 } else { 0 })) % m == (Str2Int(s.subrange(0, s.len() as int - 1)) % m * 2 + (if s[s.len() as int - 1] == '1' { 1 } else { 0 })) % m
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0) by { };
        assert(0 % m == 0) by { };
    } else {
        let last_char_bit = if s[s.len() as int - 1] == '1' { 1 } else { 0 };
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + last_char_bit) by { };
        assert((2 * Str2Int(s.subrange(0, s.len() as int - 1)) + last_char_bit) % m == (2 % m * (Str2Int(s.subrange(0, s.len() as int - 1)) % m) + last_char_bit % m) % m) by { };
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
{
    let m = Str2Int(sz@);
    let x_mod_m = Str2Int(sx@) % m;
    let y_val = Str2Int(sy@);
    
    proof {
        helper_lemma_exp_mod(Str2Int(sx@), y_val, m);
        helper_lemma_str2int_mod(sx@, m);
    }
    
    // Start with base case: x^0 mod m = 1 mod m
    let mut result = 1;
    let mut current_base = x_mod_m;
    let mut remaining_exp = y_val;
    
    while remaining_exp > 0
        invariant
            remaining_exp <= y_val,
            result * Exp_int(current_base, remaining_exp) % m == Exp_int(Str2Int(sx@), y_val) % m,
            current_base == Exp_int(x_mod_m, Exp_int(2, y_val - remaining_exp)) % m
    {
        if remaining_exp % 2 == 1 {
            result = (result * current_base) % m;
        }
        current_base = (current_base * current_base) % m;
        remaining_exp = remaining_exp / 2;
    }
    
    // Convert result to binary representation
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
    
    // Reverse to get correct order (LSB last)
    res_vec.reverse();
    
    res_vec
}
// </vc-code>

fn main() {}
}
