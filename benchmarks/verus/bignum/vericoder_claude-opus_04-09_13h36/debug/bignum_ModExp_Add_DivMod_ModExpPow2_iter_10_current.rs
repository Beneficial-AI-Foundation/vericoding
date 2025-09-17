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

proof fn lemma_str2int_recursive(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() - 1)) + 
            (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
{
    // Follows from definition
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res as nat == Str2Int(s@)
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
        
        proof {
            if i > 1 {
                lemma_str2int_recursive(s@.subrange(0, i as int));
            }
        }
    }
    
    assert(s@.subrange(0, i as int) == s@);
    result
}

spec fn ReverseStr2Int(s: Seq<char>) -> nat
    recommends ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 { 
        0 
    } else { 
        (if s[0] == '1' { 1nat } else { 0nat }) + 2 * ReverseStr2Int(s.subrange(1, s.len() as int))
    }
}

proof fn lemma_reverse_to_normal(s: Seq<char>, rev: Seq<char>)
    requires 
        ValidBitString(s),
        ValidBitString(rev),
        s.len() == rev.len(),
        forall|i: int| 0 <= i && i < s.len() ==> s[i] == rev[rev.len() - 1 - i]
    ensures Str2Int(s) == ReverseStr2Int(rev)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_reverse_to_normal(
            s.subrange(0, s.len() - 1), 
            rev.subrange(1, rev.len() as int)
        );
    }
}

exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    
    if n == 0 {
        result.push('0');
        assert(Str2Int(seq!['0']) == 0nat);
    } else {
        let mut temp = Vec::<char>::new();
        let mut m = n;
        
        // Build digits in reverse order
        while m > 0
            invariant
                ValidBitString(temp@),
                m <= n,
                n as nat == m as nat * Exp_int(2, temp@.len() as nat) + ReverseStr2Int(temp@)
        {
            if m % 2 == 1 {
                temp.push('1');
            } else {
                temp.push('0');
            }
            m = m / 2;
        }
        
        // Reverse to get correct order
        let mut i: usize = temp.len();
        while i > 0
            invariant
                i <= temp.len(),
                ValidBitString(temp@),
                ValidBitString(result@),
                result@.len() == temp@.len() - i,
                forall|j: int| 0 <= j && j < result@.len() ==> 
                    result@[j] == temp@[temp@.len() - 1 - j]
        {
            i = i - 1;
            result.push(temp[i]);
        }
        
        proof {
            lemma_reverse_to_normal(result@, temp@);
            assert(m == 0);
            assert(ReverseStr2Int(temp@) == n as nat);
        }
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
        assert(ValidBitString(sy@));
        if sy@.len() == 1 {
            assert(sy@[0] == '0' || sy@[0] == '1');
            if sy@[0] == '0' {
                assert(Str2Int(sy@) == 0);
            } else {
                assert(Str2Int(sy@) == 1);
            }
        }
        assert(Str2Int(sy@) >= 1);
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