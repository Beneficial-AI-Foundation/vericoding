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
/* helper modified by LLM (iteration 2): Added decimal_to_binary helper function */
fn decimal_to_binary(n: nat) -> Vec<char>
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        let mut digits = Vec::new();
        let mut num = n;
        while num > 0
            invariant
                num >= 0,
                ValidBitString(digits@),
                Str2Int(digits@) + num * Exp_int(2, digits@.len() as nat) == n
        {
            let bit = if num % 2 == 1 { '1' } else { '0' };
            digits.push(bit);
            num = num / 2;
        }
        digits.reverse();
        digits
    }
}

proof fn pow_div_lemma(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == (if y == 0 { 1 % z } else { (x * Exp_int(x, y - 1)) % z })
{
    if y > 0 {
        assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
    }
}

proof fn bitstring_empty_lemma()
    ensures
        Str2Int(Seq::<char>::empty()) == 0,
        ValidBitString(Seq::<char>::empty())
{
}

proof fn bitstring_cons_lemma(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1'
    ensures
        ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 })
{
}

proof fn mod_div_lemma(a: nat, b: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed decimal_to_binary calls and implementation */
{
    if sy.is_empty() {
        let mut result = Vec::<char>::new();
        result.push('1');
        proof {
            bitstring_empty_lemma();
            bitstring_cons_lemma(Seq::<char>::empty(), '1');
        }
        return result;
    }
    
    let last = sy[sy.len() - 1];
    let rest = &sy[0..sy.len() - 1];
    let rest_exp_mod = ModExp_Add_DivMod_Zeroes(sx, rest, sz);
    
    let result = if last == '1' {
        let temp_val = Str2Int(rest_exp_mod@);
        let temp_sq_val = (temp_val * temp_val) % Str2Int(sz@);
        let final_val = (temp_sq_val * Str2Int(sx@)) % Str2Int(sz@);
        decimal_to_binary(final_val)
    } else {
        let temp_val = Str2Int(rest_exp_mod@);
        let temp_sq_val = (temp_val * temp_val) % Str2Int(sz@);
        decimal_to_binary(temp_sq_val)
    };
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    return result;
}
// </vc-code>

fn main() {}
}
