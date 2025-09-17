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
/* helper modified by LLM (iteration 4): fix compilation error by replacing ghost sequence subrange with vector slicing */
exec fn str2int_exec(s: &Vec<char>) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        let last_char = s[s.len()-1];
        let rest_vec = s[0..s.len()-1].to_vec();
        let rest_val = str2int_exec(&rest_vec);
        let bit_val = if last_char == '1' { 1nat } else { 0nat };
        2nat * rest_val + bit_val
    }
}

/* helper modified by LLM (iteration 2): fix type mismatches for nat/int conversions */
exec fn nat_to_bit_vec(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@) && Str2Int(result@) == n
{
    if n == 0nat {
        vec!['0']
    } else {
        let mut bits = Vec::new();
        let mut current = n;
        while current > 0nat
            invariant current >= 0nat
            decreases current
        {
            let bit = if current % 2nat == 1nat { '1' } else { '0' };
            bits.push(bit);
            current = current / 2nat;
        }
        bits.reverse();
        bits
    }
}

/* helper modified by LLM (iteration 4): fix compilation error by replacing ghost sequence subrange with vector slicing */
exec fn mod_exp_iterative_helper(
    current_result: nat,
    current_power: nat,
    remaining_bits: &Vec<char>,
    modulus: nat,
) -> (result: nat)
    requires ValidBitString(remaining_bits@) && modulus > 1
    ensures result == (current_result * Exp_int(current_power, Str2Int(remaining_bits@))) % modulus
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
/* code modified by LLM (iteration 4): update to fixed helper functions */
{
    let sx_vec = sx.to_vec();
    let sy_vec = sy.to_vec();
    let sz_vec = sz.to_vec();
    let base_val = str2int_exec(&sx_vec);
    let mod_val = str2int_exec(&sz_vec);
    let initial_power = base_val % mod_val;
    let result_nat = mod_exp_iterative_helper(1nat, initial_power, &sy_vec, mod_val);
    nat_to_bit_vec(result_nat)
}
// </vc-code>

fn main() {}
}
