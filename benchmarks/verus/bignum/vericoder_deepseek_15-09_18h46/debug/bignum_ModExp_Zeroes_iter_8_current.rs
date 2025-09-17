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
/* helper modified by LLM (iteration 8): Fix nat literal type annotations and compilation errors */
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
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x % m, y) == (x % m) * Exp_int(x % m, (y - 1) as nat));
        assert((x * Exp_int(x, (y - 1) as nat)) % m == (x % m) * (Exp_int(x, (y - 1) as nat) % m) % m) by { };
        assert(Exp_int(x, (y - 1) as nat) % m == Exp_int(x % m, (y - 1) as nat) % m);
    }
}

proof fn helper_lemma_str2int_mod(s: Seq<char>, m: nat)
    requires ValidBitString(s), m > 1
    ensures Str2Int(s) % m == if s.len() == 0 { 0nat } else { (2 * (Str2Int(s.subrange(0, s.len() as int - 1)) % m) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat })) % m }
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(0 % m == 0);
    } else {
        let last_char_bit = if s[s.len() as int - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + last_char_bit);
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
/* code modified by LLM (iteration 8): Fix nat type mismatches and compilation errors */
{
    let m_val: nat = Str2Int(sz@);
    let x_val: nat = Str2Int(sx@);
    let y_val: nat = Str2Int(sy@);
    
    proof {
        helper_lemma_exp_mod(x_val, y_val, m_val);
    }
    
    let mut result: nat = 1nat;
    let mut current_base: nat = x_val % m_val;
    let mut remaining_exp: nat = y_val;
    
    while remaining_exp > 0nat
        invariant
            result * Exp_int(current_base, remaining_exp) % m_val == Exp_int(x_val, y_val) % m_val,
            current_base == Exp_int(x_val % m_val, Exp_int(2, (y_val - remaining_exp) as nat)) % m_val
    {
        if remaining_exp % 2nat == 1nat {
            result = (result * current_base) % m_val;
        }
        current_base = (current_base * current_base) % m_val;
        remaining_exp = remaining_exp / 2nat;
    }
    
    let mut res_vec = Vec::new();
    let mut num: nat = result;
    
    while num > 0nat
        invariant
            Str2Int(res_vec@) == num
    {
        let bit = if num % 2nat == 1nat { '1' } else { '0' };
        res_vec.push(bit);
        num = num / 2nat;
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
