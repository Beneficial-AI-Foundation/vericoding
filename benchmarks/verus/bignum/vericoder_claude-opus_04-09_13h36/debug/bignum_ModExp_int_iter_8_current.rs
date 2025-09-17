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
    } else if n == 1 {
        seq!['1']
    } else {
        Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n <= 1 {
        assert(ValidBitString(Int2Str(n)));
    } else {
        lemma_int2str_valid(n / 2);
        assert(ValidBitString(Int2Str(n)));
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        assert(Str2Int(Int2Str(0)) == 0);
    } else if n == 1 {
        assert(Str2Int(Int2Str(1)) == 1);
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        let full = Int2Str(n);
        assert(full == s.push(if n % 2 == 0 { '0' } else { '1' }));
        assert(full.subrange(0, full.len() as int - 1) == s);
        assert(full.index(full.len() as int - 1) == if n % 2 == 0 { '0' } else { '1' });
        assert(Str2Int(full) == 2 * Str2Int(s) + if n % 2 == 0 { 0nat } else { 1nat });
        assert(Str2Int(full) == 2 * (n / 2) + n % 2);
        assert(2 * (n / 2) + n % 2 == n);
    }
}

exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
    decreases n
{
    proof { 
        lemma_int2str_valid(n as nat);
        lemma_str2int_int2str(n as nat);
    }
    
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    } else if n == 1 {
        let mut v = Vec::new();
        v.push('1');
        return v;
    } else {
        let mut v = int_to_str(n / 2);
        if n % 2 == 0 {
            v.push('0');
        } else {
            v.push('1');
        }
        return v;
    }
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() > 0
    ensures res == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 1 {
        if s[0] == '1' {
            return 1;
        } else {
            return 0;
        }
    } else {
        let n = s.len() - 1;
        let mut prefix = Vec::new();
        for i in 0..n
            invariant 
                n == s.len() - 1,
                i <= n,
                prefix@.len() == i,
                forall |j: int| 0 <= j && j < i ==> prefix@[j] == s@[j]
        {
            prefix.push(s[i]);
        }
        assert(prefix@ == s@.subrange(0, n as int));
        let val = str_to_int(&prefix);
        assert(val == Str2Int(prefix@));
        
        if s[n] == '1' {
            return 2 * val + 1;
        } else {
            return 2 * val;
        }
    }
}

proof fn lemma_exp_mod_mult(a: nat, b: nat, c: nat, m: nat)
    requires m > 1
    ensures ((a % m) * (b % m) * c) % m == (a * b * c) % m
{
}

proof fn lemma_exp_split(x: nat, y: nat)
    requires y > 0
    ensures 
        if y % 2 == 0 {
            Exp_int(x, y) == Exp_int(x * x, y / 2)
        } else {
            Exp_int(x, y) == x * Exp_int(x * x, y / 2)
        }
    decreases y
{
    if y == 1 {
        assert(Exp_int(x, 1) == x);
        assert(y / 2 == 0);
        assert(Exp_int(x * x, 0) == 1);
    } else if y % 2 == 0 {
        assert(y >= 2);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        if y > 2 {
            lemma_exp_split(x, (y - 2) as nat);
        }
        assert(Exp_int(x, (y - 2) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
        assert((y - 2) / 2 == y / 2 - 1);
        assert(Exp_int(x * x, y / 2) == (x * x) * Exp_int(x * x, (y / 2 - 1) as nat));
    } else {
        assert(y % 2 == 1);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert((y - 1) % 2 == 0);
        lemma_exp_split(x, (y - 1) as nat);
        assert(Exp_int(x, (y - 1) as nat) == Exp_int(x * x, ((y - 1) / 2) as nat));
        assert((y - 1) / 2 == y / 2);
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
    let x_val = str_to_int(sx);
    let y_val = str_to_int(sy);
    let z_val = str_to_int(sz);
    
    let mut result: u64 = 1;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant 
            z_val == Str2Int(sz@),
            z_val > 1,
            x_val == Str2Int(sx@),
            y_val == Str2Int(sy@),
            base < z_val,
            result < z_val,
            ((result as nat) * Exp_int(base as nat, exp as nat)) % (z_val as nat) == 
                Exp_int(x_val as nat, y_val as nat) % (z_val as nat)
        decreases exp
    {
        proof {
            lemma_exp_split(base as nat, exp as nat);
        }
        
        if exp % 2 == 1 {
            result = (result * base) % z_val;
            proof {
                lemma_exp_mod_mult(result as nat, base as nat, Exp_int((base * base) as nat % (z_val as nat), (exp / 2) as nat), z_val as nat);
            }
        }
        
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    assert(exp == 0);
    assert(Exp_int(base as nat, 0) == 1);
    assert(result == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
    
    let res = int_to_str(result);
    
    proof {
        lemma_int2str_valid(result as nat);
        lemma_str2int_int2str(result as nat);
    }
    
    res
}
// </vc-code>

fn main() {}
}