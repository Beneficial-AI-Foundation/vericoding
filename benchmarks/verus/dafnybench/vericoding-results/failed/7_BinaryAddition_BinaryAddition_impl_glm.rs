use vstd::prelude::*;

verus! {

/* 
MIPS 0
We implement the following with bitvectors in Verus.
here s' and t' are converted to decimal scalars
s = [1,1,1], t = [1,0,1], ys = [1, 0, 0], s' = 7, t' = 5, ys' = 4
ys' % 2 ^ (len(s)) = (s' + t') % 2 ^ (len(s))
4 % 8 = 12 % 8

def f(s,t):
    a = 0;b = 0;
    ys = []
    for i in range(10):
        c = s[i]; d = t[i];
        next_a = b ^ c ^ d
        next_b = b+c+d>1
        a = next_a;b = next_b;
        y = a
        ys.append(y)
    return ys
*/

// Helper function to check if a bit is set
spec fn is_bit_set(x: u16, bit_index: int) -> bool
    recommends 0 <= bit_index < 10
{
    (x & (1u16 << bit_index)) != 0
}

// Convert u16 to sequence of 10 bools (LSB first)
spec fn bv10_to_seq(x: u16) -> Seq<bool> {
    seq![
        is_bit_set(x, 0), is_bit_set(x, 1), is_bit_set(x, 2), is_bit_set(x, 3),
        is_bit_set(x, 4), is_bit_set(x, 5), is_bit_set(x, 6), is_bit_set(x, 7),
        is_bit_set(x, 8), is_bit_set(x, 9)
    ]
}

// Convert array of bools to u16 bitvector
spec fn array_to_bv10(arr: &[bool; 10]) -> u16
{
    array_to_bv10_helper(arr, 9)
}

spec fn array_to_bv10_helper(arr: &[bool; 10], index: nat) -> u16
    recommends index < 10
    decreases index
{
    if index == 0 {
        if arr[index as int] { 1u16 } else { 0u16 }
    } else {
        let bit: u16 = if arr[index as int] { 1u16 } else { 0u16 };
        #[verifier::truncate]
        let shifted: u16 = (bit << (index as int));
        #[verifier::truncate]
        let result: u16 = (shifted as int + array_to_bv10_helper(arr, (index - 1) as nat) as int) as u16;
        result
    }
}

// Convert array to sequence
fn array_to_sequence(arr: &[bool; 10]) -> (res: Vec<bool>)
    ensures res.len() == 10,
    ensures forall|k: int| 0 <= k < 10 ==> res[k] == arr[k]
{
    assume(false);
    Vec::new()
}

// Boolean to integer conversion
spec fn bool_to_int(a: bool) -> int {
    if a { 1 } else { 0 }
}

// XOR operation
spec fn xor_bool(a: bool, b: bool) -> bool {
    (a || b) && !(a && b)
}

// Traditional bit addition using bitvectors
spec fn bit_addition(s: &[bool; 10], t: &[bool; 10]) -> Seq<bool> {
    let a: u16 = array_to_bv10(s);
    let b: u16 = array_to_bv10(t);
    #[verifier::truncate]
    let c: u16 = (a as int + b as int) as u16;
    bv10_to_seq(c)
}

// <vc-helpers>
// Convert the first k elements of a vector to a natural number (LSB first)
spec fn vector_slice_to_nat_low(v: &Vec<bool>, k: nat) -> nat
    recommends 0 <= k <= v.len()
    decreases k
{
    if k == 0 {
        0
    } else {
        let n = k - 1;
        let bit_val = if v@[n] { 1 } else { 0 };
        let power = 1 << n;
        bit_val * power + vector_slice_to_nat_low(v, n)
    }
}

// Convert the first k elements of an array to a natural number (LSB first)
spec fn array_slice_to_nat_low(arr: &[bool; 10], k: nat) -> nat
    recommends 0 <= k <= 10
    decreases k
{
    if k == 0 {
        0
    } else {
        let n = k - 1;
        let bit_val = if arr@[n] { 1 } else { 0 };
        let power = 1 << n;
        bit_val * power + array_slice_to_nat_low(arr, n)
    }
}

// Function to convert boolean to u16
spec fn bool_to_u16(b: bool) -> u16 {
    if b { 1u16 } else { 0u16 }
}

// Function to convert sequence of booleans to u16 (LSB first)
spec fn seq_to_bv10(s: Seq<bool>) -> u16
    recommends s.len() == 10
{
    seq_to_bv10_helper(s, 0)
}

spec fn seq_to_bv10_helper(s: Seq<bool>, i: int) -> u16
    recommends 0 <= i <= 10
    decreases 10 - i
{
    if i == 10 {
        0u16
    } else {
        let bit = bool_to_u16(s@[i]);
        #[verifier::truncate]
        let shifted = bit << i;
        #[verifier::truncate]
        let result = shifted + seq_to_bv10_helper(s, i + 1);
        result
    }
}

// Lemma relating array_slice_to_nat_low and bit_addition
proof fn lemma_array_nat_low_bit_addition(s: &[bool; 10], t: &[bool; 10], k: nat)
    requires 0 <= k <= 10
    ensures array_slice_to_nat_low(s, k) + array_slice_to_nat_low(t, k) < nat::pow(2, k + 1)
{
    if k == 0 {
    } else {
        lemma_array_nat_low_bit_addition(s, t, k - 1);
    }
}

// Lemma to establish equality between vector elements and bit addition result
proof fn lemma_vector_equals_bit_addition(s: &[bool; 10], t: &[bool; 10], result: &Vec<bool>)
    requires result.len() == 10
    requires forall|i: int| 0 <= i < 10 ==> result@[i] == bit_addition(s, t)@[i]
    ensures bit_addition(s, t) == result@
{
    assert(forall|i: int| 0 <= i < 10 ==> result@[i] == bit_addition(s, t)@[i]);
}
// </vc-helpers>

// <vc-spec>
fn binary_addition(s: &[bool; 10], t: &[bool; 10]) -> (sresult: Vec<bool>) // Generated program for bit addition
    requires s.len() == 10 && t.len() == 10
    ensures sresult.len() == 10,
    ensures bit_addition(s, t) == sresult@, // Verification of correctness
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<bool> = Vec::new();
    let mut carry: bool = false;

    for i in 0..10
        invariant
            result.len() == i,
            0 <= i <= 10,
            vector_slice_to_nat_low(&result, i) + (if carry { nat::pow(2, i) } else { 0 }) 
                == array_slice_to_nat_low(s, i) + array_slice_to_nat_low(t, i),
            forall|j: int| 0 <= j < i ==> result@[j] == bit_addition(s, t)@[j]
    {
        let a = s[i];
        let b = t[i];
        let total = bool_to_int(a) + bool_to_int(b) + bool_to_int(carry);
        let result_bit = total % 2 == 1;
        let new_carry = total >= 2;

        proof {
            assert(bool_to_int(a) + bool_to_int(b) + bool_to_int(carry) >= 0);
            assert(bool_to_int(a) + bool_to_int(b) + bool_to_int(carry) <= 3);
            assert(total % 2 == (bool_to_int(a) + bool_to_int(b) + bool_to_int(carry)) % 2);
        }

        result.push(result_bit);
        carry = new_carry;
        
        proof {
            assert(result@[i] == bit_addition(s, t)@[i]);
        }
    }
    
    proof {
        lemma_vector_equals_bit_addition(s, t, &result);
    }

    result
}
// </vc-code>

fn main() {
}

}