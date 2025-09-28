// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) + str2int(s2)
{
    assume(false);
    unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
        (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
        sy.len() == n + 1 &&
        str2int(sz) > 1
    ensures 
        valid_bit_string(res) &&
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
    decreases n
{
    assume(false);
    unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) * str2int(s2)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed issue by removing the helper as it was not needed for the mod_exp implementation. The helper section is intentionally left blank because no additional helper functions are necessary for the current task. */
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
        sy.len() > 0 && str2int(sz) > 1
    ensures 
        valid_bit_string(res) &&
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
    decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Refactored the `mod_exp` function. Explicitly handled the base case where `sy.len() == 1`. Modified the recursive call for `mod_exp` to pass `sy.subrange(0, (y_len - 1) as int)` instead of `y_prefix_seq` directly since `y_prefix_seq` wasn't being used. Corrected the base case handling for `final_val_nat` conversion. Added a loop to convert `final_val_nat` to a sequence of characters directly. This transformation helps avoid conflicts and ensures that the helper function `int_to_seq_char_recursive` doesn't need to be created. This implementation works recursively and provides a solution for the modulus exponentiation using the specific `str2int` implementation for binary string conversion. */
{
    let X_nat = str2int(sx);
    let Y_val_nat = str2int(sy);
    let Z_nat = str2int(sz);

    if Y_val_nat == 0 {
        return (Seq::<char>::new() + '1');
    }

    let y_len = sy.len();
    
    // Base case: if sy has only one bit (0 or 1)
    if y_len == 1 {
        let last_bit_char = sy[0];
        let last_bit_nat = if last_bit_char == '1' { 1nat } else { 0nat };

        let final_val_nat = if last_bit_nat == 1 {
            X_nat % Z_nat
        } else {
            1nat % Z_nat
        };

        if final_val_nat == 0 {
            return (Seq::<char>::new() + '0');
        }

        let mut bits: Seq<char> = Seq::new();
        let mut current_nat_val = final_val_nat;
        while current_nat_val > 0 {
            let remainder = current_nat_val % 2;
            if remainder == 1 {
                bits = bits.push('1');
            } else {
                bits = bits.push('0');
            }
            current_nat_val = current_nat_val / 2;
        }

        let mut reversed_bits = Seq::<char>::new();
        let mut i = bits.len() as int - 1;
        while i >= 0 
            invariant
                0 <= i + 1 <= bits.len(),
                reversed_bits.len() == bits.len() as int - 1 - i
            decreases i
        {
            reversed_bits = reversed_bits.push(bits[i as usize]);
            i = i - 1;
        }
        return reversed_bits;
    }

    let last_bit_char: char = sy[ (y_len - 1) as usize ];
    let last_bit_nat: nat = if last_bit_char == '1' { 1nat } else { 0nat };

    // Recursive call for Y/2 (integer division)
    let temp_res = mod_exp(sx, sy.subrange(0, (y_len - 1) as int), sz);
    let temp_res_val = str2int(temp_res);

    let squared_val = (temp_res_val * temp_res_val) % Z_nat;
    let final_val_nat;

    if last_bit_nat == 1 {
        final_val_nat = (squared_val * X_nat) % Z_nat;
    } else {
        final_val_nat = squared_val;
    }

    // Convert final_val_nat to Seq<char>
    if final_val_nat == 0 {
        return (Seq::<char>::new() + '0');
    }

    let mut bits: Seq<char> = Seq::new();
    let mut current_nat_val = final_val_nat;
    while current_nat_val > 0 {
        let remainder = current_nat_val % 2;
        if remainder == 1 {
            bits = bits.push('1');
        } else {
            bits = bits.push('0');
        }
        current_nat_val = current_nat_val / 2;
    }

    // Reverse the bits to get the correct order
    let mut reversed_bits = Seq::<char>::new();
    let mut i = bits.len() as int - 1;
    while i >= 0 
        invariant
            0 <= i + 1 <= bits.len(),
            reversed_bits.len() == bits.len() as int - 1 - i
        decreases i
    {
        reversed_bits = reversed_bits.push(bits[i as usize]);
        i = i - 1;
    }
    reversed_bits
}
// </vc-code>


}

fn main() {}