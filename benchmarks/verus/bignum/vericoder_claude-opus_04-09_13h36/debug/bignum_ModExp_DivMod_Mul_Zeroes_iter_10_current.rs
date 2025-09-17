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
// Helper lemmas for modular arithmetic
proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    // Proof by SMT solver
}

proof fn lemma_exp_unfold(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    // By definition of Exp_int
}

proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
    // By definition of Exp_int
}

proof fn lemma_str2int_empty()
    ensures Str2Int(seq![]) == 0
{
    // By definition
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    assert(s.push('0').len() == s.len() + 1);
    assert(s.push('0').subrange(0, s.len() as int) =~= s);
    assert(s.push('0').index(s.len() as int) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    assert(s.push('1').len() == s.len() + 1);
    assert(s.push('1').subrange(0, s.len() as int) =~= s);
    assert(s.push('1').index(s.len() as int) == '1');
}

proof fn lemma_str2int_all_zeros(s: Seq<char>)
    requires 
        ValidBitString(s),
        forall |j: int| 0 <= j && j < s.len() ==> s[j] == '0',
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
        lemma_str2int_empty();
    } else {
        assert(s.index(s.len() as int - 1) == '0');
        let prefix = s.subrange(0, s.len() as int - 1);
        assert(forall |j: int| 0 <= j && j < prefix.len() ==> prefix[j] == '0');
        lemma_str2int_all_zeros(prefix);
        assert(Str2Int(s) == 2 * Str2Int(prefix) + 0);
        assert(Str2Int(s) == 2 * 0 + 0);
        assert(Str2Int(s) == 0);
    }
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
    decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * Exp_int(x, 1));
        assert(Exp_int(x, 1) == x * Exp_int(x, 0));
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x, 2) == x * x);
        assert(Exp_int(x * x, 1) == x * x);
    } else {
        assert(y >= 2);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        lemma_exp_even(x, (y - 2) as nat);
    }
}

// Convert nat to bit string
exec fn nat_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(Str2Int(result@) == 0);
        }
        return result;
    }
    
    let mut m = n;
    while m > 0
        invariant
            0 <= m <= n,
            ValidBitString(result@),
    {
        if m % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        m = m / 2;
    }
    
    // Reverse the result
    let mut i: usize = 0;
    let mut j = result.len() - 1;
    while i < j
        invariant
            0 <= i <= result.len(),
            0 <= j < result.len(),
            i + j == result.len() - 1,
            ValidBitString(result@),
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        if j > 0 { j = j - 1; }
    }
    
    return result;
}

// Multiply two bit strings modulo z
exec fn multiply_mod(a: &[char], b: &[char], z: &[char]) -> (res: Vec<char>)
    requires 
        ValidBitString(a@),
        ValidBitString(b@),
        ValidBitString(z@),
        Str2Int(z@) > 1,
    ensures 
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(a@) * Str2Int(b@)) % Str2Int(z@),
{
    let a_val = Str2Int(a@);
    let b_val = Str2Int(b@);
    let z_val = Str2Int(z@);
    let product = (a_val * b_val) % z_val;
    
    proof {
        lemma_mod_mul(a_val, b_val, z_val);
    }
    
    nat_to_bitstring(product)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Check if y represents zero
    let mut all_zero = true;
    let mut i: usize = 0;
    while i < sy.len()
        invariant
            0 <= i <= sy.len(),
            all_zero <==> (forall |j: int| 0 <= j && j < i ==> sy@[j] == '0'),
    {
        if sy[i] != '0' {
            all_zero = false;
        }
        i = i + 1;
    }
    
    if all_zero {
        proof { 
            lemma_str2int_all_zeros(sy@);
            assert(Str2Int(sy@) == 0);
            lemma_exp_zero(Str2Int(sx@));
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        let mut res = Vec::<char>::new();
        res.push('1');
        proof {
            assert(ValidBitString(res@));
            assert(Str2Int(res@) == 1);
            assert(1 % Str2Int(sz@) < Str2Int(sz@));
        }
        return res;
    }
    
    // Recursive case
    let last_idx = sy.len() - 1;
    if sy[last_idx] == '0' {
        // y is even: compute (x^(y/2))^2 mod z
        let mut y_half = Vec::<char>::new();
        let mut j: usize = 0;
        while j < last_idx
            invariant
                0 <= j <= last_idx,
                y_half@.len() == j,
                ValidBitString(y_half@),
                forall |k: int| 0 <= k && k < j ==> y_half@[k] == sy@[k],
        {
            y_half.push(sy[j]);
            j = j + 1;
        }
        
        proof {
            assert(y_half@ =~= sy@.subrange(0, sy@.len() as int - 1));
            assert(sy@[sy@.len() as int - 1] == '0');
            assert(Str2Int(sy@) == 2 * Str2Int(y_half@));
            lemma_exp_even(Str2Int(sx@), Str2Int(sy@));
        }
        
        let half_result = ModExp_DivMod_Mul_Zeroes(sx, &y_half, sz);
        
        proof {
            assert(Str2Int(half_result@) == Exp_int(Str2Int(sx@), Str2Int(y_half@)) % Str2Int(sz@));
        }
        
        // Compute (half_result * half_result) mod z
        let result = multiply_mod(&half_result, &half_result, sz);
        
        proof {
            lemma_mod_mul(Str2Int(half_result@), Str2Int(half_result@), Str2Int(sz@));
            assert(Str2Int(result@) == (Str2Int(half_result@) * Str2Int(half_result@)) % Str2Int(sz@));
        }
        
        return result;
    } else {
        // y is odd: compute x * (x^(y-1)) mod z
        let mut y_minus_one = Vec::<char>::new();
        let mut j: usize = 0;
        while j < last_idx
            invariant
                0 <= j <= last_idx,
                y_minus_one@.len() == j,
                ValidBitString(y_minus_one@),
                forall |k: int| 0 <= k && k < j ==> y_minus_one@[k] == sy@[k],
        {
            y_minus_one.push(sy[j]);
            j = j + 1;
        }
        y_minus_one.push('0');
        
        proof {
            assert(sy@[sy@.len() as int - 1] == '1');
            assert(Str2Int(sy@) == 2 * Str2Int(sy@.subrange(0, sy@.len() as int - 1)) + 1);
            lemma_str2int_append_zero(sy@.subrange(0, sy@.len() as int - 1));
            assert(Str2Int(y_minus_one@) == Str2Int(sy@) - 1);
            lemma_exp_unfold(Str2Int(sx@), Str2Int(sy@));
        }
        
        let rec_result = ModExp_DivMod_Mul_Zeroes(sx, &y_minus_one, sz);
        
        proof {
            assert(Str2Int(rec_result@) == Exp_int(Str2Int(sx@), Str2Int(y_minus_one@)) % Str2Int(sz@));
            assert(Str2Int(y_minus_one@) == Str2Int(sy@) - 1);
        }
        
        // Compute (x * rec_result) mod z
        let result = multiply_mod(sx, &rec_result, sz);
        
        proof {
            lemma_mod_mul(Str2Int(sx@), Str2Int(rec_result@), Str2Int(sz@));
            assert(Str2Int(result@) == (Str2Int(sx@) * Str2Int(rec_result@)) % Str2Int(sz@));
        }
        
        return result;
    }
}
// </vc-code>

fn main() {}
}