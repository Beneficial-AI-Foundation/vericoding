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
// Helper function to convert an integer to a binary string
spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

// Lemma: Converting back and forth preserves the value
proof fn lemma_int2str_str2int(n: nat)
    ensures ValidBitString(Int2Str(n)),
    ensures Str2Int(Int2Str(n)) == n,
    decreases n,
{
    if n == 0 {
        assert(Int2Str(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else if n == 1 {
        assert(Int2Str(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        lemma_int2str_str2int(n / 2);
        let s = Int2Str(n / 2);
        assert(ValidBitString(s));
        if n % 2 == 0 {
            assert(Int2Str(n) == s.push('0'));
            assert(Str2Int(s.push('0')) == 2 * Str2Int(s) + 0);
        } else {
            assert(Int2Str(n) == s.push('1'));
            assert(Str2Int(s.push('1')) == 2 * Str2Int(s) + 1);
        }
    }
}

// Helper to compute modular multiplication
exec fn mod_mul(a: nat, b: nat, m: nat) -> (res: nat)
    requires m > 1,
    ensures res == (a * b) % m,
{
    ((a % m) * (b % m)) % m
}

// Helper to convert nat to Vec<char> binary string
exec fn nat_to_binary_vec(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
    ensures Str2Int(res@) == n,
{
    if n == 0 {
        proof { lemma_int2str_str2int(0); }
        return vec!['0'];
    }
    
    let mut result = Vec::new();
    let mut temp = n;
    
    while temp > 0
        invariant temp <= n,
        invariant forall |i: int| 0 <= i && i < result@.len() ==> (result@[i] == '0' || result@[i] == '1'),
    {
        if temp % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        temp = temp / 2;
    }
    
    // Reverse the result to get most significant bit first
    let mut reversed = Vec::new();
    let mut i = result.len();
    while i > 0
        invariant 0 <= i <= result.len(),
        invariant reversed@.len() == result@.len() - i,
        invariant forall |j: int| 0 <= j && j < reversed@.len() ==> 
            reversed@[j] == result@[result@.len() - 1 - j],
        invariant forall |j: int| 0 <= j && j < reversed@.len() ==> 
            (reversed@[j] == '0' || reversed@[j] == '1'),
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    
    proof {
        lemma_int2str_str2int(n);
    }
    
    reversed
}

// Helper to decrement a binary string by 1
exec fn decrement_binary(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@),
    requires Str2Int(s@) > 0,
    ensures ValidBitString(res@),
    ensures Str2Int(res@) == Str2Int(s@) - 1,
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    // Copy the input
    while i < s.len()
        invariant i <= s.len(),
        invariant result@.len() == i,
        invariant forall |j: int| 0 <= j && j < i ==> result@[j] == s@[j],
        invariant forall |j: int| 0 <= j && j < i ==> (result@[j] == '0' || result@[j] == '1'),
    {
        result.push(s[i]);
        i = i + 1;
    }
    
    // Perform the decrement from right to left
    let mut j = result.len() - 1;
    let mut done = false;
    
    while !done && j < result.len()
        invariant j < result.len(),
        invariant ValidBitString(result@),
    {
        if result[j] == '1' {
            result.set(j, '0');
            done = true;
        } else {
            result.set(j, '1');
            if j == 0 {
                done = true;
            } else {
                j = j - 1;
            }
        }
    }
    
    // Remove leading zeros if any
    while result.len() > 1 && result[0] == '0'
        invariant result@.len() >= 1,
        invariant ValidBitString(result@),
    {
        result.remove(0);
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if sy@.len() == 1 && sy@[0] == '0' {
        // x^0 = 1
        assert(y_val == 0);
        assert(Exp_int(x_val, 0) == 1);
        let res = nat_to_binary_vec(1 % z_val);
        assert(Str2Int(res@) == 1 % z_val);
        assert(Str2Int(res@) == Exp_int(x_val, 0) % z_val);
        return res;
    }
    
    // y > 0 case
    assert(y_val > 0);
    
    // Create y-1 in binary
    let sy_minus_1_vec = decrement_binary(sy);
    assert(ValidBitString(sy_minus_1_vec@));
    assert(Str2Int(sy_minus_1_vec@) == y_val - 1);
    
    // Recursive call
    let rec_result = ModExp_DivMod_Mul(sx, &sy_minus_1_vec, sz);
    let rec_val = Str2Int(rec_result@);
    
    assert(rec_val == Exp_int(x_val, y_val - 1) % z_val);
    
    // Compute final result: (rec_val * x_val) % z_val
    let final_val = mod_mul(rec_val, x_val % z_val, z_val);
    
    assert(final_val == (rec_val * x_val) % z_val);
    assert(final_val == ((Exp_int(x_val, y_val - 1) % z_val) * x_val) % z_val);
    assert(final_val == (Exp_int(x_val, y_val - 1) * x_val) % z_val);
    assert(Exp_int(x_val, y_val) == x_val * Exp_int(x_val, y_val - 1));
    assert(final_val == Exp_int(x_val, y_val) % z_val);
    
    let res = nat_to_binary_vec(final_val);
    assert(Str2Int(res@) == final_val);
    assert(Str2Int(res@) == Exp_int(x_val, y_val) % z_val);
    
    res
}
// </vc-code>

fn main() {}
}