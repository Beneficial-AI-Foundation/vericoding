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
fn array_to_sequence(arr: &[bool; 10]) -> (res: Vec<bool>)
    ensures res.len() == 10,
    ensures forall |k: int| 0 <= k && k < 10 ==> res[k as usize] == arr[k as usize]
{
    // Implementation that constructs the Vec<bool> from the array
    let mut v: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < 10 {
        invariant 0 <= i && i <= 10;
        invariant v.len() == (i as usize);
        invariant forall |k: int| 0 <= k && k < i ==> v[k as usize] == arr[k as usize];
        v.push(arr[i as usize]);
        i += 1;
    }
    assert(v.len() == 10);
    assert(forall |k: int| 0 <= k && k < 10 ==> v[k as usize] == arr[k as usize]);
    v
}

fn array_to_bv10_runtime(arr: &[bool; 10]) -> (res: u16)
    ensures res == array_to_bv10(arr)
{
    let mut res: u16 = 0u16;
    let mut i: int = 0;
    while i < 10 {
        invariant 0 <= i && i <= 10;
        invariant if i == 0 { res == 0u16 } else { res == array_to_bv10_helper(arr, (i - 1) as nat) };
        let idx: usize = i as usize;
        if arr[idx] {
            let bit: u16 = 1u16 << (i as int);
            #[verifier::truncate]
            res = (res as int + bit as int) as u16;
        }
        i += 1;
    }
    // At loop exit, i == 10, so res == array_to_bv10_helper(arr, 9) == array_to_bv10(arr)
    assert(res == array_to_bv10_helper(arr, 9));
    assert(res == array_to_bv10(arr));
    res
}

fn bv10_to_vec(x: u16) -> (res: Vec<bool>)
    ensures res.len() == 10,
    ensures bv10_to_seq(x) == res@
{
    let mut v: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < 10 {
        invariant 0 <= i && i <= 10;
        invariant v.len() == (i as usize);
        invariant forall |k: int| 0 <= k && k < i ==> v[k as usize] == bv10_to_seq(x)@[k as usize];
        let bit: bool = (x & (1u16 << (i as int))) != 0;
        v.push(bit);
        i += 1;
    }
    assert(v.len() == 10);
    assert(forall |k: int| 0 <= k && k < 10 ==> v[k as usize] == bv10_to_seq(x)@[k as usize]);
    v
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
    let a: u16 = array_to_bv10_runtime(s);
    let b: u16 = array_to_bv10_runtime(t);
    #[verifier::truncate]
    let c: u16 = (a as int + b as int) as u16;
    let mut res_vec: Vec<bool> = bv10_to_vec(c);

    // relate runtime values to spec definitions
    assert(a == array_to_bv10(s));
    assert(b == array_to_bv10(t));
    #[verifier::truncate]
    assert(c == (array_to_bv10(s) as int + array_to_bv10(t) as int) as u16);
    // bit_addition(s,t) is defined as bv10_to_seq of that sum
    assert(bit_addition(s, t) == bv10_to_seq(c));
    // bv10_to_vec ensures equality with bv10_to_seq
    assert(res_vec@ == bv10_to_seq(c));

    res_vec
}
// </vc-code>

fn main() {
}

}