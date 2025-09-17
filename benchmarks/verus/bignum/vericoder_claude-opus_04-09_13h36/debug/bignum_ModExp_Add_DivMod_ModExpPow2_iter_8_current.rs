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
proof fn lemma_exp_split(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    // Follows directly from the definition of Exp_int
}

proof fn lemma_exp_mod_base(x: nat, y: nat, m: nat)
    requires m > 0
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x % m, 0) == 1);
    } else {
        lemma_exp_split(x, y);
        lemma_exp_split(x % m, y);
        lemma_exp_mod_base(x, (y - 1) as nat, m);
        assert((x * Exp_int(x, (y - 1) as nat)) % m == ((x % m) * (Exp_int(x, (y - 1) as nat) % m)) % m);
        assert((x % m * Exp_int(x % m, (y - 1) as nat)) % m == ((x % m) * (Exp_int(x % m, (y - 1) as nat) % m)) % m);
    }
}

proof fn lemma_mod_mul_assoc(a: nat, b: nat, c: nat, m: nat)
    requires m > 0
    ensures ((a % m) * (b % m)) % m == (a * b) % m
{
}

proof fn lemma_exp_mod_odd(base: nat, exp: nat, result: nat, m: nat)
    requires m > 1, exp > 0, exp % 2 == 1, result < m, base < m
    ensures ((result * base) % m * Exp_int((base * base) % m, exp / 2)) % m == 
            (result * Exp_int(base, exp)) % m
{
    lemma_exp_split(base, exp);
    assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    assert((exp - 1) % 2 == 0);
    
    if exp == 1 {
        assert(Exp_int(base, 1) == base);
        assert(exp / 2 == 0);
        assert(Exp_int((base * base) % m, 0) == 1);
    } else {
        assert(exp - 1 == 2 * (exp / 2));
        lemma_exp_mod_even_helper(base, (exp - 1) as nat, m);
    }
}

proof fn lemma_exp_mod_even_helper(base: nat, exp: nat, m: nat)
    requires m > 0, exp > 0, exp % 2 == 0
    ensures Exp_int(base, exp) % m == Exp_int((base * base) % m, exp / 2) % m
    decreases exp
{
    if exp == 2 {
        assert(Exp_int(base, 2) == base * base);
        assert(Exp_int((base * base) % m, 1) % m == ((base * base) % m) % m);
    } else {
        lemma_exp_split(base, exp);
        lemma_exp_split(base, (exp - 1) as nat);
        assert(exp >= 4);
        lemma_exp_mod_even_helper(base, (exp - 2) as nat, m);
    }
}

proof fn lemma_exp_mod_even(base: nat, exp: nat, result: nat, m: nat)
    requires m > 1, exp > 0, exp % 2 == 0, result < m, base < m
    ensures (result * Exp_int((base * base) % m, exp / 2)) % m == 
            (result * Exp_int(base, exp)) % m
{
    lemma_exp_mod_even_helper(base, exp, m);
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res as nat == Str2Int(s@)
    decreases s@.len()
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@),
            result as nat == Str2Int(s@.subrange(0, i as int))
    {
        let digit = if s[i] == '1' { 1u64 } else { 0u64 };
        result = result * 2 + digit;
        i = i + 1;
        
        assert(s@.subrange(0, i as int) == s@.subrange(0, (i - 1) as int).push(s@[i - 1]));
    }
    
    assert(s@.subrange(0, i as int) == s@);
    result
}

exec fn int_to_str(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
    let original_n = n;
    let mut result = Vec::<char>::new();
    
    if n == 0 {
        result.push('0');
    } else {
        while n > 0
            invariant
                ValidBitString(result@),
                n as nat * Exp_int(2, result@.len() as nat) + Str2Int(result@.reverse()) == original_n as nat
        {
            if n % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            n = n / 2;
        }
        
        result.reverse();
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = str_to_int(sx);
    let y_int = str_to_int(sy);
    let z_int = str_to_int(sz);
    
    assert(y_int > 0) by {
        assert(sy@.len() > 0);
    }
    
    let mut result: u64 = 1;
    let mut base = x_int % z_int;
    let mut exp = y_int;
    
    proof {
        lemma_exp_mod_base(x_int as nat, y_int as nat, z_int as nat);
    }
    
    while exp > 0
        invariant 
            z_int > 1,
            result < z_int,
            base < z_int,
            (result as nat * Exp_int(base as nat, exp as nat)) % (z_int as nat) == 
                Exp_int(x_int as nat, y_int as nat) % (z_int as nat)
        decreases exp
    {
        if exp % 2 == 1 {
            proof {
                lemma_exp_mod_odd(base as nat, exp as nat, result as nat, z_int as nat);
            }
            result = (result * base) % z_int;
            base = (base * base) % z_int;
            exp = exp / 2;
        } else {
            proof {
                lemma_exp_mod_even(base as nat, exp as nat, result as nat, z_int as nat);
            }
            base = (base * base) % z_int;
            exp = exp / 2;
        }
    }
    
    assert(exp == 0);
    assert(Exp_int(base as nat, 0) == 1);
    assert(result as nat == Exp_int(x_int as nat, y_int as nat) % (z_int as nat));
    
    int_to_str(result)
}
// </vc-code>

fn main() {}
}