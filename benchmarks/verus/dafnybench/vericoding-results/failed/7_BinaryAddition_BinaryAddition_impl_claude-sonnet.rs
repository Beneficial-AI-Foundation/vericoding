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
// Helper lemma for array to sequence conversion
proof fn lemma_array_to_sequence_correct(arr: &[bool; 10], res: &Vec<bool>)
    requires res.len() == 10,
    requires forall|k: int| 0 <= k < 10 ==> res[k] == arr[k]
    ensures res@ == seq![arr[0], arr[1], arr[2], arr[3], arr[4], arr[5], arr[6], arr[7], arr[8], arr[9]]
{
    assert(res@.len() == 10);
    assert(res@[0] == arr[0]);
    assert(res@[1] == arr[1]);
    assert(res@[2] == arr[2]);
    assert(res@[3] == arr[3]);
    assert(res@[4] == arr[4]);
    assert(res@[5] == arr[5]);
    assert(res@[6] == arr[6]);
    assert(res@[7] == arr[7]);
    assert(res@[8] == arr[8]);
    assert(res@[9] == arr[9]);
}

// Helper for bit addition correctness
proof fn lemma_bit_addition_step(s: &[bool; 10], t: &[bool; 10], i: usize, a: bool, b: bool, result: &Vec<bool>)
    requires i < 10,
    requires result.len() == 10,
    requires a == s[i as int],
    requires b == t[i as int],
    ensures true
{
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
    let mut final_result = Vec::new();
    let mut j = 0;
    while j < 10
        invariant 0 <= j <= 10,
        invariant final_result.len() == j,
        invariant forall|k: int| 0 <= k < j ==> final_result[k] == is_bit_set(((array_to_bv10(s) as int + array_to_bv10(t) as int) as u16), k),
    {
        let s_bv = array_to_bv10(s);
        let t_bv = array_to_bv10(t);
        #[verifier::truncate]
        let sum_bv = ((s_bv as int + t_bv as int) as u16);
        let bit_val = is_bit_set(sum_bv, j as int);
        final_result.push(bit_val);
        j += 1;
    }
    
    proof {
        assert(final_result.len() == 10);
        let s_bv = array_to_bv10(s);
        let t_bv = array_to_bv10(t);
        let sum_bv = ((s_bv as int + t_bv as int) as u16);
        let expected = bv10_to_seq(sum_bv);
        
        assert(expected.len() == 10);
        assert(forall|k: int| 0 <= k < 10 ==> final_result[k] == is_bit_set(sum_bv, k));
        assert(forall|k: int| 0 <= k < 10 ==> expected[k] == is_bit_set(sum_bv, k));
        assert(forall|k: int| 0 <= k < 10 ==> final_result[k] == expected[k]);
        assert(final_result@ =~= expected);
        assert(bit_addition(s, t) == final_result@);
    }
    
    final_result
}
// </vc-code>

fn main() {
}

}