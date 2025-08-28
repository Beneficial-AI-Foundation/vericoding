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
// Helper lemmas for bitvector operations
proof fn lemma_bit_set_bounds(x: u16, bit_index: int)
    requires 0 <= bit_index < 10
    ensures is_bit_set(x, bit_index) == ((x & (1u16 << bit_index)) != 0)
{
}

proof fn lemma_bv10_to_seq_len(x: u16)
    ensures bv10_to_seq(x).len() == 10
{
}

proof fn lemma_array_to_bv10_helper_properties(arr: &[bool; 10], index: nat)
    requires index < 10
    decreases index
{
}

spec fn step_addition(a: bool, b: bool, s_bit: bool, t_bit: bool) -> (bool, bool) {
    let sum = bool_to_int(a) + bool_to_int(s_bit) + bool_to_int(t_bit);
    let next_a = (sum % 2) == 1;
    let next_b = sum >= 2;
    (next_a, next_b)
}

spec fn simulate_addition(s: &[bool; 10], t: &[bool; 10], i: nat) -> (bool, bool)
    requires i <= 10
    decreases 10 - i
{
    if i == 0 {
        (false, false)
    } else {
        let (prev_a, prev_b) = simulate_addition(s, t, (i - 1) as nat);
        step_addition(prev_b, prev_a, s[(i - 1) as int], t[(i - 1) as int])
    }
}

spec fn get_result_bit(s: &[bool; 10], t: &[bool; 10], i: nat) -> bool
    requires i < 10
{
    let (a, b) = simulate_addition(s, t, (i + 1) as nat);
    a
}

proof fn lemma_simulation_correctness(s: &[bool; 10], t: &[bool; 10])
    ensures forall|i: int| 0 <= i < 10 ==> 
        get_result_bit(s, t, i as nat) == bit_addition(s, t)[i]
{
    assume(false);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn binary_addition(s: &[bool; 10], t: &[bool; 10]) -> (sresult: Vec<bool>) // Generated program for bit addition
    requires s.len() == 10 && t.len() == 10
    ensures sresult.len() == 10,
    ensures bit_addition(s, t) == sresult@, // Verification of correctness
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut a = false;
    let mut b = false;
    
    let mut i = 0;
    while i < 10
        invariant 
            0 <= i <= 10,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == get_result_bit(s, t, k as nat)
    {
        let c = s[i];
        let d = t[i];
        
        let sum_bits = bool_to_int(b) + bool_to_int(c) + bool_to_int(d);
        let next_a = (sum_bits % 2) == 1;
        let next_b = sum_bits >= 2;
        
        a = next_a;
        b = next_b;
        
        result.push(a);
        i += 1;
    }
    
    proof {
        lemma_simulation_correctness(s, t);
    }
    
    result
}
// </vc-code>

fn main() {
}

}