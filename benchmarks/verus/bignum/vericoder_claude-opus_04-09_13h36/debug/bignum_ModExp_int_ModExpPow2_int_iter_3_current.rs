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
// Helper function to convert nat to binary string
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

// Helper lemmas for conversion properties
proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n > 1 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n > 1 {
        lemma_str2int_int2str(n / 2);
        reveal(Str2Int);
        reveal(Int2Str);
    }
}

// Helper to compute (a * b) mod m
exec fn mul_mod(a: nat, b: nat, m: nat) -> (res: nat)
    requires m > 0
    ensures res == (a * b) % m
{
    ((a % m) * (b % m)) % m
}

// Helper to compute a^2 mod m
exec fn square_mod(a: nat, m: nat) -> (res: nat)
    requires m > 0
    ensures res == (a * a) % m
{
    mul_mod(a, a, m)
}

// Convert binary string to nat
exec fn str_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0nat
    } else {
        let rest = str_to_nat(&s[..s.len() - 1]);
        let last_bit = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
        proof {
            assert(s@.subrange(0, s@.len() as int - 1) == s[..s.len() - 1]@);
            assert(s@.index(s@.len() as int - 1) == s[s.len() - 1]);
        }
        2 * rest + last_bit
    }
}

// Convert nat to binary string
exec fn nat_to_str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n
    decreases n
{
    proof {
        lemma_int2str_valid(n);
        lemma_str2int_int2str(n);
    }
    
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        proof {
            assert(v@ == seq!['0']);
            assert(Int2Str(0) == seq!['0']);
        }
        v
    } else if n == 1 {
        let mut v = Vec::new();
        v.push('1');
        proof {
            assert(v@ == seq!['1']);
            assert(Int2Str(1) == seq!['1']);
        }
        v
    } else {
        let mut v = nat_to_str(n / 2);
        if n % 2 == 0 {
            v.push('0');
        } else {
            v.push('1');
        }
        proof {
            assert(v@ == Int2Str(n));
        }
        v
    }
}

// Modular exponentiation helper
exec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1, exp > 0
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 1 {
        proof {
            assert(Exp_int(base, 1) == base);
        }
        base % modulus
    } else {
        let half = mod_exp_helper(base, exp / 2, modulus);
        let squared = square_mod(half, modulus);
        
        proof {
            assert(exp / 2 > 0) by {
                assert(exp > 1);
            }
            assert(Exp_int(base, exp / 2) % modulus == half);
            assert((half * half) % modulus == squared);
        }
        
        if exp % 2 == 0 {
            proof {
                assert(exp == 2 * (exp / 2));
                assert(Exp_int(base, exp) == Exp_int(base, 2 * (exp / 2)));
                assert(Exp_int(base, 2 * (exp / 2)) == base * Exp_int(base, 2 * (exp / 2) - 1)) by {
                    reveal(Exp_int);
                }
                assert(2 * (exp / 2) - 1 == 2 * (exp / 2) - 1);
                lemma_exp_split(base, exp / 2);
            }
            squared
        } else {
            proof {
                assert(exp == 2 * (exp / 2) + 1);
                assert(Exp_int(base, exp) == base * Exp_int(base, exp - 1)) by {
                    reveal(Exp_int);
                }
                assert(exp - 1 == 2 * (exp / 2));
                lemma_exp_split(base, exp / 2);
                assert(Exp_int(base, 2 * (exp / 2)) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
            }
            mul_mod(squared, base, modulus)
        }
    }
}

proof fn lemma_exp_split(base: nat, k: nat)
    ensures Exp_int(base, 2 * k) == Exp_int(base, k) * Exp_int(base, k)
    decreases k
{
    if k == 0 {
        assert(Exp_int(base, 0) == 1) by { reveal(Exp_int); }
        assert(Exp_int(base, 0) * Exp_int(base, 0) == 1);
        assert(2 * 0 == 0);
        assert(Exp_int(base, 2 * 0) == 1) by { reveal(Exp_int); }
    } else {
        assert(Exp_int(base, 2 * k) == base * Exp_int(base, 2 * k - 1)) by { reveal(Exp_int); }
        assert(2 * k - 1 == 2 * k - 1);
        if k == 1 {
            assert(Exp_int(base, 2) == base * Exp_int(base, 1)) by { reveal(Exp_int); }
            assert(Exp_int(base, 1) == base) by { reveal(Exp_int); }
            assert(Exp_int(base, 2) == base * base);
        } else {
            lemma_exp_recursive_double(base, k);
        }
    }
}

proof fn lemma_exp_recursive_double(base: nat, k: nat)
    requires k > 0
    ensures Exp_int(base, 2 * k) == Exp_int(base, k) * Exp_int(base, k)
    decreases k
{
    if k == 1 {
        assert(Exp_int(base, 2) == base * base) by {
            reveal(Exp_int);
            assert(Exp_int(base, 2) == base * Exp_int(base, 1));
            assert(Exp_int(base, 1) == base);
        }
        assert(Exp_int(base, 1) == base) by { reveal(Exp_int); }
    } else {
        reveal(Exp_int);
        assert(Exp_int(base, k) == base * Exp_int(base, k - 1));
        lemma_exp_add(base, k, k);
    }
}

proof fn lemma_exp_add(base: nat, a: nat, b: nat)
    ensures Exp_int(base, a + b) == Exp_int(base, a) * Exp_int(base, b)
    decreases b
{
    if b == 0 {
        assert(Exp_int(base, 0) == 1) by { reveal(Exp_int); }
        assert(a + 0 == a);
    } else {
        reveal(Exp_int);
        assert(Exp_int(base, b) == base * Exp_int(base, b - 1));
        assert(Exp_int(base, a + b) == base * Exp_int(base, a + b - 1));
        assert(a + b - 1 == a + (b - 1));
        lemma_exp_add(base, a, b - 1);
        assert(Exp_int(base, a + (b - 1)) == Exp_int(base, a) * Exp_int(base, b - 1));
    }
}

proof fn lemma_str2int_positive(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) > 0 || (s.len() == 1 && s[0] == '0')
    decreases s.len()
{
    if s.len() == 1 {
        reveal(Str2Int);
        if s[0] == '1' {
            assert(Str2Int(s) == 1);
        } else {
            assert(s[0] == '0');
            assert(Str2Int(s) == 0);
        }
    } else {
        reveal(Str2Int);
        let prefix = s.subrange(0, s.len() as int - 1);
        if prefix.len() > 0 {
            lemma_str2int_positive(prefix);
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = str_to_nat(sx);
    let y_val = str_to_nat(sy);
    let z_val = str_to_nat(sz);
    
    proof {
        assert(y_val > 0) by {
            assert(sy@.len() > 0);
            lemma_str2int_positive(sy@);
        }
    }
    
    let result_val = if y_val == 0 {
        proof {
            assert(Exp_int(x_val, 0) == 1) by { reveal(Exp_int); }
        }
        1 % z_val
    } else {
        mod_exp_helper(x_val, y_val, z_val)
    };
    
    let result = nat_to_str(result_val);
    
    proof {
        assert(Str2Int(result@) == result_val);
        assert(result_val == Exp_int(x_val, y_val) % z_val);
        assert(x_val == Str2Int(sx@));
        assert(y_val == Str2Int(sy@));
        assert(z_val == Str2Int(sz@));
    }
    
    result
}
// </vc-code>

fn main() {}
}