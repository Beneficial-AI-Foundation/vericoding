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
/* helper modified by LLM (iteration 10): Fixed decimal_to_binary function signature and added Vec conversion helpers */
fn decimal_to_binary(n: nat) -> (s: Vec<char>)
    ensures ValidBitString(s@), Str2Int(s@) == n
{
    if n == 0 {
        Vec::new()
    } else {
        let rest = decimal_to_binary(n / 2);
        let digit = if n % 2 == 1 { '1' } else { '0' };
        let mut result = rest.clone();
        result.push(digit);
        result
    }
}

proof fn decimal_to_binary_valid(n: nat)
    ensures ValidBitString(decimal_to_binary(n)@)
{
    if n > 0 {
        decimal_to_binary_valid(n / 2);
    }
}

proof fn decimal_to_binary_correct(n: nat)
    ensures Str2Int(decimal_to_binary(n)@) == n
{
    if n > 0 {
        decimal_to_binary_correct(n / 2);
    }
}

proof fn bitstring_cons_lemma(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s + Seq::new(1, c)), Str2Int(s + Seq::new(1, c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 })
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
/* code modified by LLM (iteration 10): Fixed result variable and Vec handling */
{
    if sy.is_empty() {
        let mut result = Vec::<char>::new();
        result.push('1');
        proof {
            bitstring_cons_lemma(Seq::<char>::empty(), '1');
        }
        return result;
    }
    
    let last = sy[sy.len() - 1];
    let rest = &sy[0..sy.len() - 1];
    let rest_exp_mod = ModExp_Add_DivMod_Zeroes(sx, rest, sz);
    
    if last == '1' {
        let temp_val = Str2Int(rest_exp_mod@);
        let temp_sq_val = (temp_val * temp_val) % Str2Int(sz@);
        let final_val = (temp_sq_val * Str2Int(sx@)) % Str2Int(sz@);
        let result = decimal_to_binary(final_val);
        proof {
            decimal_to_binary_valid(final_val);
            decimal_to_binary_correct(final_val);
        }
        result
    } else {
        let temp_val = Str2Int(rest_exp_mod@);
        let temp_sq_val = (temp_val * temp_val) % Str2Int(sz@);
        let result = decimal_to_binary(temp_sq_val);
        proof {
            decimal_to_binary_valid(temp_sq_val);
            decimal_to_binary_correct(temp_sq_val);
        }
        result
    }
}
// </vc-code>

fn main() {}
}
