// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fix type errors for `nat` and `f64` comparison, ensuring correct usage of Verus primitives. */
fn count_digits_and_decimal(x: f64) -> (res: (nat, nat))
    requires
        x.abs() >= 0.0,
    ensures
        // The two nat values are (number of integer digits, number of fractional digits)
        res.0 >= 1,
{
    let abs_x = x.abs();

    // Separate integer and fractional parts
    let integer_part = abs_x as u128;
    let fractional_part = abs_x - integer_part as f64;

    // Count digits in the integer part
    let mut integer_digits: nat = 0nat;
    let mut temp_int = integer_part;
    if temp_int == 0 {
        integer_digits = 1nat;
    } else {
        while temp_int > 0
            invariant
                temp_int >= 0,
                integer_digits <= 39nat, // Max u128 digits
            decreases temp_int
        {
            temp_int = temp_int / 10;
            integer_digits = integer_digits + 1nat;
        }
    }

    // Count digits in the fractional part with consideration for trailing zeros
    let mut fractional_digits: nat = 0nat;
    if fractional_part > 0.0 {
        let mut current_fraction = fractional_part;
        let mut precision_factor: u128 = 1;

        // Loop to find the necessary precision to accurately represent the fractional part
        // We'll limit this to a reasonable number to avoid infinite loops with non-terminating decimals
        // For IEEE 754 double-precision, typically up to 17 decimal digits are meaningful.
        while fractional_digits < 17nat
            invariant
                fractional_digits <= 17nat,
                precision_factor > 0,
            decreases 17nat - fractional_digits
        {
            precision_factor = precision_factor * 10;
            let multiplied_fraction = current_fraction * precision_factor as f64;
            let rounded_fraction = (multiplied_fraction + 0.5) as u128;

            // Check if multiplying by precision_factor makes it an integer
            let is_integer_after_multiply = multiplied_fraction == rounded_fraction as f64;
            // Also check for tiny errors that might make `multiplied_fraction - rounded_fraction as f64` non-zero but very close to zero.
            // We'll consider it an integer if the error is tiny, e.g., less than epsilon.
            let epsilon = 1e-9; // A small value for floating point comparisons
            let is_integer_close = (multiplied_fraction - rounded_fraction as f64).abs() < epsilon;

            if is_integer_after_multiply || is_integer_close {
                fractional_digits = fractional_digits + 1nat;
                // Now, remove trailing zeros
                let mut temp_frac_u128 = rounded_fraction;
                let mut trailing_zeros: nat = 0nat;
                if temp_frac_u128 == 0 {
                    // If the fractional part was like 0.0, we just count 0 digits
                    // or if it was say 0.500, we count 1 digit if reduced to 0.5
                    // For 0.0, fractional_part = 0.0, so this block won't be entered.
                    // For 0.5, rounded_fraction would be 5, not 0.
                } else {
                    while temp_frac_u128 > 0 && temp_frac_u128 % 10 == 0
                        invariant
                            temp_frac_u128 >= 0,
                           trailing_zeros <= 17nat, // Max fractional digits
                        decreases temp_frac_u128
                    {
                        temp_frac_u128 = temp_frac_u128 / 10;
                        trailing_zeros = trailing_zeros + 1nat;
                    }
                }
                fractional_digits = fractional_digits - trailing_zeros;
                break;
            }
            fractional_digits = fractional_digits + 1nat;
        }
    }

    (integer_digits, fractional_digits)
}
// </vc-helpers>

// <vc-spec>
fn format_float(x: f64, parens: bool) -> (result: String)
    ensures
        result@.len() > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed `nat` and `usize`/`u32` casts for formatting. */
{
    let (integer_digits, fractional_digits) = count_digits_and_decimal(x);
    let is_negative = x < 0.0;
    let abs_x = x.abs();

    let mut s = String::new();

    if parens {
        s.push('(');
    }

    if is_negative {
        s.push('-');
    }

    // Format integer part
    let integer_part = abs_x as u128;
    let integer_str = integer_part.to_string();
    s.push_str(&integer_str);

    // Format fractional part if present
    if fractional_digits > 0nat {
        s.push('.');
        let fractional_digits_u32 = fractional_digits as u32;
        let fractional_part_scaled = (abs_x - integer_part as f64) * (10u128.pow(fractional_digits_u32)) as f64;
        let fractional_part_u128 = (fractional_part_scaled + 0.5) as u128;

        let fractional_digits_usize = fractional_digits as usize;
        let fractional_str_full = format!("{:0width$}", fractional_part_u128, width = fractional_digits_usize);
        s.push_str(&fractional_str_full);
    }

    if parens {
        s.push(')');
    }

    s
}
// </vc-code>


}
fn main() {}