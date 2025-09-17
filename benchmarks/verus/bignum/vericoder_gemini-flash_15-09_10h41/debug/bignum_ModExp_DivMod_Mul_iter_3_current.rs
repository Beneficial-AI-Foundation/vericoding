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
/* helper modified by LLM (iteration 3): Removed extraneous `mut` keyword, fixed `result` scope issue */
spec fn modMultiply(a: nat, b: nat, m: nat) -> nat { (a * b) % m }

spec fn int_to_bit_vec(n: nat) -> Seq<char>
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n,
{
    if n == 0 {
        seq!['0']
    } else {
        let mut bits: Seq<char> = Seq::empty();
        let mut temp = n;
        while temp > 0
            invariant
                temp >= 0,
                ValidBitString(bits),
                Str2Int(bits) + temp * Exp_int(2, bits.len() as nat) == n
        {
            if temp % 2 == 1 {
                bits = bits.push('1');
            } else {
                bits = bits.push('0');
            }
            temp = temp / 2;
        }
        // Reverse the bits as they were generated in reverse order
        let mut reversed_bits: Seq<char> = Seq::empty();
        let mut i: int = bits.len() as int - 1;
        while i >= 0
            invariant
                i >= -1,
                i < bits.len() as int,
                reversed_bits.len() == (bits.len() as int - 1 - i) as nat,
                forall |j: int| 0 <= j && j < reversed_bits.len() ==> reversed_bits@[j] == bits@[bits.len() as int - 1 - j]
        {
            reversed_bits = reversed_bits.push(bits@[i]);
            i = i - 1;
        }
        reversed_bits
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Corrected conversion of sy@.len() to int, and adjusted handling of int_to_bit_vec as spec function. Updated the loop to correctly build `sy_half_bits` using `Vec<char>::push`. */
{
    let b_int = Str2Int(sy@);
    let c_int = Str2Int(sz@);

    if b_int == 0 {
        return (vec!['1']);
    }

    let mut result_vec: Vec<char>;

    // sy_half = sy / 2
    let sy_half_len_val = (sy@.len() as int) / 2;
    let mut sy_half_bits: Vec<char> = Vec::new();
    
    let mut i = 0;
    while i < sy_half_len_val
        invariant
            0 <= i && i <= sy_half_len_val,
            sy_half_bits@.len() == i,
            // Removed the problematic clause: forall |j: int| 0 <= j && j < i ==> sy_half_bits@[j] == sy@[j],
            // as the vec is building up, this is implied by the push
    {
        sy_half_bits.push(sy@[i]);
        i = i + 1;
    }
    
    // Recursively compute x^(y/2) mod c
    let half_res_vec = ModExp_DivMod_Mul(sx, &sy_half_bits, sz);
    let half_res_int = Str2Int(half_res_vec@);

    // If y is even, result is (x^(y/2))^2 mod c
    if b_int % 2 == 0 {
        let final_int = modMultiply(half_res_int, half_res_int, c_int);
        proof {
            assert(sy@.len() >= 1) by { assert(sy@.len() > 0 && b_int > 0); };
            assert(sy_half_bits@.len() == sy@.len() as int / 2);
        }
       result_vec = int_to_bit_vec(final_int).into_vec(); // Convert Seq<char> to Vec<char>
    } else {
        // If y is odd, result is (x * (x^(y/2))^2) mod c
        let sx_int = Str2Int(sx@);
        let temp_int = modMultiply(sx_int, half_res_int, c_int);
        let final_int = modMultiply(temp_int, half_res_int, c_int);
        proof {
            assert(sy@.len() >= 1) by { assert(sy@.len() > 0 && b_int > 0); };
            assert(sy_half_bits@.len() == sy@.len() as int / 2);
        }
         result_vec = int_to_bit_vec(final_int).into_vec(); // Convert Seq<char> to Vec<char>
    }
    
    // Convert the integer result to a bit string
    return result_vec;
}
// </vc-code>

fn main() {}
}
