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
/* helper modified by LLM (iteration 6): replace nat types with ghost code in spec functions and exec functions */
spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }) }
}

/* helper modified by LLM (iteration 6): make exec function compatible with exec mode by using int instead of nat */
exec fn str2int_exec(s: &Vec<char>) -> (result: int)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@) as int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_char = s[s.len()-1];
        let rest_vec = s[0..s.len()-1].to_vec();
        let rest_val = str2int_exec(&rest_vec);
        let bit_val = if last_char == '1' { 1 } else { 0 };
        2 * rest_val + bit_val
    }
}

/* helper modified by LLM (iteration 6): make exec function compatible with exec mode by using int instead of nat */
exec fn nat_to_bit_vec(n: int) -> (result: Vec<char>)
    requires n >= 0
    ensures ValidBitString(result@) && Str2Int(result@) as int == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut bits = Vec::new();
        let mut current = n;
        while current > 0
            invariant current >= 0
            decreases current
        {
            let bit = if current % 2 == 1 { '1' } else { '0' };
            bits.push(bit);
            current = current / 2;
        }
        bits.reverse();
        bits
    }
}

/* helper modified by LLM (iteration 6): make exec function compatible with exec mode by using int instead of nat */
exec fn mod_exp_iterative_helper(
    current_result: int,
    current_power: int,
    remaining_bits: &Vec<char>,
    modulus: int,
) -> (result: int)
    requires ValidBitString(remaining_bits@) && modulus > 1 && current_result >= 0 && current_power >= 0
    ensures result == ((current_result as nat * Exp_int(current_power as nat, Str2Int(remaining_bits@))) % modulus as nat) as int
    decreases remaining_bits.len()
{
    if remaining_bits.len() == 0 {
        current_result % modulus
    } else {
        let next_bit = remaining_bits[0];
        let rest_vec = remaining_bits[1..].to_vec();

        let new_result = if next_bit == '1' {
            (current_result * current_power) % modulus
        } else {
            current_result
        };

        let new_power = (current_power * current_power) % modulus;

        mod_exp_iterative_helper(new_result, new_power, &rest_vec, modulus)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): replace nat types with int types throughout the implementation */
{
    let sx_vec = sx.to_vec();
    let sy_vec = sy.to_vec();
    let sz_vec = sz.to_vec();
    let base_val = str2int_exec(&sx_vec);
    let mod_val = str2int_exec(&sz_vec);
    let initial_power = base_val % mod_val;
    let result_nat = mod_exp_iterative_helper(1, initial_power, &sy_vec, mod_val);
    nat_to_bit_vec(result_nat)
}
// </vc-code>

fn main() {}
}
