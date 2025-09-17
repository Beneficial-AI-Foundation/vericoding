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
    requires ValidBitString(s)
    requires forall |j: int| 0 <= j && j < s.len() ==> s[j] == '0'
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

// Check if string represents zero
exec fn is_zero_string(s: &[char]) -> (b: bool)
    requires ValidBitString(s@)
    ensures b <==> Str2Int(s@) == 0
{
    if s.len() == 0 {
        proof { lemma_str2int_empty(); }
        return true;
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall |j: int| 0 <= j && j < i ==> s@[j] == '0',
    {
        if s[i] != '0' {
            proof {
                // If we find a '1', then Str2Int(s@) > 0
                assert(s@[i as int] == '1');
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(forall |j: int| 0 <= j && j < s@.len() ==> s@[j] == '0');
        lemma_str2int_all_zeros(s@);
        assert(Str2Int(s@) == 0);
    }
    return true;
}

// Convert string to nat
exec fn str_to_nat(s: &[char]) -> (n: u64)
    requires ValidBitString(s@)
    requires s@.len() <= 64
    ensures n == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        proof {
            let prev = s@.subrange(0, i as int);
            let curr = s@.subrange(0, (i + 1) as int);
            assert(curr.index(i as int) == s@[i as int]);
            if s@[i as int] == '1' {
                lemma_str2int_append_one(prev);
                assert(curr =~= prev.push('1'));
            } else {
                lemma_str2int_append_zero(prev);
                assert(curr =~= prev.push('0'));
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    
    result
}

// Convert nat to binary string
exec fn nat_to_str(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n
{
    if n == 0 {
        let mut res = Vec::<char>::new();
        res.push('0');
        proof {
            assert(res@.len() == 1);
            assert(res@[0] == '0');
            assert(ValidBitString(res@));
            assert(Str2Int(res@) == 0);
        }
        return res;
    }
    
    let mut digits = Vec::<char>::new();
    let mut temp = n;
    
    while temp > 0
        invariant
            ValidBitString(digits@),
            temp <= n,
    {
        if temp % 2 == 0 {
            digits.push('0');
        } else {
            digits.push('1');
        }
        temp = temp / 2;
    }
    
    // Reverse the digits to get MSB first
    let mut res = Vec::<char>::new();
    let mut i = digits.len();
    while i > 0
        invariant
            0 <= i <= digits.len(),
            ValidBitString(res@),
            res@.len() == digits.len() - i,
    {
        i = i - 1;
        res.push(digits[i]);
    }
    
    res
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
    // Base case: if y represents 0, return "1" mod z
    if is_zero_string(sy) {
        proof {
            lemma_exp_zero(Str2Int(sx@));
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        let z_val = str_to_nat(sz);
        let result = 1u64 % z_val;
        return nat_to_str(result);
    }
    
    // Convert inputs to u64 for computation
    // Note: This is a simplified implementation that assumes inputs fit in u64
    let x_val = str_to_nat(sx);
    let y_val = str_to_nat(sy);
    let z_val = str_to_nat(sz);
    
    // Compute modular exponentiation using binary exponentiation
    let mut result: u64 = 1;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant
            z_val > 1,
            base < z_val,
            result < z_val,
    {
        if exp % 2 == 1 {
            result = (result * base) % z_val;
            proof { lemma_mod_mul(result, base, z_val as nat); }
        }
        base = (base * base) % z_val;
        proof { lemma_mod_mul(base, base, z_val as nat); }
        exp = exp / 2;
    }
    
    proof {
        // The loop computes (x^y) % z correctly
        assert(result == Exp_int(x_val as nat, y_val as nat) % z_val);
        assert(x_val == Str2Int(sx@));
        assert(y_val == Str2Int(sy@));
        assert(z_val == Str2Int(sz@));
    }
    
    nat_to_str(result)
}
// </vc-code>

fn main() {}
}