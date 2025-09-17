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
/* helper modified by LLM (iteration 7): Remove ghost code from executable section and add proper proof helpers */
proof fn lemma_str2int_rec(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 })
    decreases s.len()
{
    if s.len() > 0 {
        lemma_str2int_rec(s.subrange(0, s.len() as int - 1), s.index(s.len() as int - 1));
    }
}

proof fn lemma_mul_mod(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn lemma_add_mod(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a + b) % m == ((a % m) + (b % m)) % m
{
}

proof fn lemma_exp_mod(x: nat, y: nat, m: nat)
    requires m > 0
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
    decreases y
{
    if y > 0 {
        lemma_exp_mod(x, (y - 1) as nat, m);
        lemma_mul_mod(x, Exp_int(x, (y - 1) as nat), m);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Remove ghost code from executable section and use proper u64 arithmetic */
{
    let mut y_val: u64 = 0;
    let mut x_val: u64 = 0;
    let mut z_val: u64 = 0;
    
    // Convert input bit strings to executable u64 values
    for i in 0..sx.len() {
        x_val = x_val * 2 + if sx[i] == '1' { 1 } else { 0 };
    }
    
    for i in 0..sy.len() {
        y_val = y_val * 2 + if sy[i] == '1' { 1 } else { 0 };
    }
    
    for i in 0..sz.len() {
        z_val = z_val * 2 + if sz[i] == '1' { 1 } else { 0 };
    }
    
    // Modular exponentiation using executable u64 arithmetic
    let mut result_val: u64 = 1;
    let mut temp_val: u64 = x_val % z_val;
    let mut exp: u64 = y_val;
    
    while exp > 0 {
        if exp % 2 == 1 {
            result_val = (result_val * temp_val) % z_val;
        }
        temp_val = (temp_val * temp_val) % z_val;
        exp = exp / 2;
    }
    
    // Convert result back to bit string
    let mut result_chars = Vec::new();
    let mut val: u64 = result_val;
    
    if val == 0 {
        result_chars.push('0');
    } else {
        while val > 0 {
            if val % 2 == 1 {
                result_chars.push('1');
            } else {
                result_chars.push('0');
            }
            val = val / 2;
        }
        result_chars.reverse();
    }
    
    result_chars
}
// </vc-code>

fn main() {}
}
