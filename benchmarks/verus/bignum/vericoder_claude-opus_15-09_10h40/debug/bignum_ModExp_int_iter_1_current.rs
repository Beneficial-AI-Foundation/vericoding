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
spec fn Int2Str(n: nat) -> Seq<char>
decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        Int2Str_helper(n)
    }
}

spec fn Int2Str_helper(n: nat) -> Seq<char>
recommends n > 0
decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        Int2Str_helper(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures
        n > 0 ==> Str2Int(Int2Str(n)) == n,
        ValidBitString(Int2Str(n)),
    decreases n
{
    if n == 0 {
    } else {
        lemma_str2int_int2str_helper(n);
    }
}

proof fn lemma_str2int_int2str_helper(n: nat)
    requires n > 0
    ensures
        Str2Int(Int2Str_helper(n)) == n,
        ValidBitString(Int2Str_helper(n)),
    decreases n
{
    if n == 1 {
        assert(Int2Str_helper(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        lemma_str2int_int2str_helper(n / 2);
        let s = Int2Str_helper(n / 2);
        let c = if n % 2 == 0 { '0' } else { '1' };
        let s_new = s.push(c);
        assert(s_new.subrange(0, s_new.len() as int - 1) == s);
        assert(s_new.index(s_new.len() as int - 1) == c);
        assert(Str2Int(s_new) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 }));
        assert(Str2Int(s_new) == 2 * (n / 2) + n % 2);
        assert(2 * (n / 2) + n % 2 == n);
    }
}

exec fn str2int_exec(s: &[char]) -> (res: usize)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
    {
        result = result * 2 + if s[i] == '1' { 1 } else { 0 };
        i = i + 1;
    }
    assert(s@.subrange(0, s.len() as int) == s@);
    result
}

exec fn int2str_exec(mut n: usize) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
{
    if n == 0 {
        let mut v = Vec::<char>::new();
        v.push('0');
        proof {
            assert(v@ == seq!['0']);
            assert(Str2Int(seq!['0']) == 0);
        }
        return v;
    }
    
    let mut result = Vec::<char>::new();
    let orig_n = n;
    
    while n > 0
        invariant
            n <= orig_n,
            orig_n > 0,
            n > 0 ==> Str2Int(Int2Str_helper(n).add(result@)) == orig_n,
            n == 0 ==> Str2Int(result@) == orig_n,
            ValidBitString(result@),
        decreases n
    {
        let bit = if n % 2 == 0 { '0' } else { '1' };
        let old_result = result;
        let old_n = n;
        result.insert(0, bit);
        n = n / 2;
        
        proof {
            lemma_str2int_int2str_helper(old_n);
            if n > 0 {
                lemma_str2int_int2str_helper(n);
            }
            assert(result@ == seq![bit].add(old_result@));
        }
    }
    
    proof {
        lemma_str2int_int2str(orig_n);
    }
    result
}

exec fn modexp_helper(base: usize, exp: usize, modulus: usize) -> (res: usize)
    requires
        modulus > 1,
    ensures
        res == Exp_int(base, exp) % modulus,
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else {
        let half = modexp_helper(base, exp / 2, modulus);
        let mut result = (half * half) % modulus;
        if exp % 2 == 1 {
            result = (result * base) % modulus;
        }
        proof {
            if exp % 2 == 0 {
                assert(Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
            } else {
                assert(Exp_int(base, exp) == base * Exp_int(base, exp - 1));
                assert(exp - 1 == 2 * (exp / 2));
                assert(Exp_int(base, exp - 1) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
            }
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = str2int_exec(sx);
    let y_val = str2int_exec(sy);
    let z_val = str2int_exec(sz);
    
    let result_val = modexp_helper(x_val, y_val, z_val);
    
    let result = int2str_exec(result_val);
    
    proof {
        lemma_str2int_int2str(result_val);
    }
    
    result
}
// </vc-code>

fn main() {}
}
