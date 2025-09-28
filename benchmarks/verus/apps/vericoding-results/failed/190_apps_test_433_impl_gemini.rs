// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int, a: int, b: int) -> bool {
        n >= 1 && 1 <= a <= n && -100 <= b <= 100
    }
    
    spec fn final_entrance(n: int, a: int, b: int) -> int {
        ((a - 1 + b) % n + n) % n + 1
    }
    
    spec fn valid_output(result: int, n: int) -> bool {
        1 <= result <= n
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect path for vstd lemma and simplified ensures clause */
proof fn lemma_mod_pattern_equivalence_i32(val: i32, m: i32)
    requires m > 0
    ensures
        ((val % m + m) % m) as int == (val as int) % (m as int),
{
    // The Verus `int` type's % operator is mathematical mod.
    // The Rust `i32` type's % operator is mathematical rem (remainder).
    // This lemma proves that the `(val % m + m) % m` pattern on `i32`s
    // is equivalent to the mathematical mod on the corresponding `int`s.
    // `lemma_rem_to_mod` proves `x % m == (x rem m + m) rem m` for `int`s.
    // Verus automatically lifts the `i32` operations to `int` operations
    // where `i32::%` becomes `int::rem`, so calling this lemma is sufficient.
    vstd::arithmetic::mod_internals::lemma_rem_to_mod(val as int, m as int);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int)
    ensures 
        valid_output(result as int, n as int),
        result as int == final_entrance(n as int, a as int, b as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No change to logic, only updating comment. */
{
    // Use i32 for intermediate calculations to prevent overflow. `a - 1 + b` can
    // exceed the i8 range (e.g., if a=127, b=100, then a-1+b = 226 > 127).
    let n_i32 = n as i32;
    let a_i32 = a as i32;
    let b_i32 = b as i32;

    let displaced_pos = a_i32 - 1 + b_i32;

    // Prove that the i32 implementation of the modulo pattern is equivalent to the
    // `int` version in the `final_entrance` spec function.
    lemma_mod_pattern_equivalence_i32(displaced_pos, n_i32);

    // The `(x % n + n) % n` pattern correctly computes the mathematical modulo,
    // ensuring the result is in the range [0, n-1].
    let final_pos_0_indexed = (displaced_pos % n_i32 + n_i32) % n_i32;
    
    // Convert back to 1-based indexing for the final result.
    let result = final_pos_0_indexed + 1;

    // The result is in the range [1, n], and since n <= 127, it safely fits in an i8.
    result as i8
}
// </vc-code>


}

fn main() {}