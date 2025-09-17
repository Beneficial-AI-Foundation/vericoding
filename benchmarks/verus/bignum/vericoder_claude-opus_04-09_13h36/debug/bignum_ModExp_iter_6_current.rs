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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
proof fn lemma_exp_mod(x: nat, y: nat, z: nat)
    requires y > 0, z > 1
    ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    reveal(Exp_int);
    assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
}

proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
    reveal(Exp_int);
}

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
        let s = Int2Str(n / 2);
        let result = s.push(if n % 2 == 0 { '0' } else { '1' });
        assert forall |i: int| 0 <= i && i < result.len() as int implies
            result.index(i) == '0' || result.index(i) == '1' by {
            if i < s.len() as int {
                assert(result.index(i) == s.index(i));
            } else {
                assert(i == s.len() as int);
                assert(result.index(i) == (if n % 2 == 0 { '0' } else { '1' }));
            }
        }
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        reveal(Str2Int);
        assert(Int2Str(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else if n == 1 {
        reveal(Str2Int);
        assert(Int2Str(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        let c = if n % 2 == 0 { '0' } else { '1' };
        let result = s.push(c);
        assert(Int2Str(n) == result);
        
        lemma_int2str_valid(n / 2);
        assert(ValidBitString(s));
        assert(ValidBitString(result));
        
        assert(result.subrange(0, result.len() as int - 1) == s);
        assert(result.index(result.len() as int - 1) == c);
        
        assert(Str2Int(result) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })) by {
            reveal(Str2Int);
        }
        assert(Str2Int(s) == n / 2);
        assert(Str2Int(result) == 2 * (n / 2) + (if n % 2 == 0 { 0nat } else { 1nat }));
        assert(Str2Int(result) == n);
    }
}

exec fn str2int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 
            i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        let old_result = result;
        result = result * 2;
        
        if s[i] == '1' {
            result = result + 1;
        }
        
        assert(s@.subrange(0, (i + 1) as int).subrange(0, i as int) == s@.subrange(0, i as int));
        assert(s@.subrange(0, (i + 1) as int).index(i as int) == s@.index(i as int));
        assert(Str2Int(s@.subrange(0, (i + 1) as int)) == 
               2 * Str2Int(s@.subrange(0, i as int)) + 
               (if s@.index(i as int) == '1' { 1nat } else { 0nat })) by {
            reveal(Str2Int);
        }
        
        i = i + 1;
    }
    
    assert(s@.subrange(0, s@.len() as int) == s@);
    result
}

exec fn int2str_exec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        
        proof {
            lemma_int2str_valid(0nat);
            lemma_str2int_int2str(0nat);
            assert(Int2Str(0) == seq!['0']);
            assert(v@ == Int2Str(0));
        }
        
        return v;
    }
    
    let mut v = Vec::new();
    let mut m = n;
    
    while m > 0
        invariant 
            n > 0,
            ValidBitString(v@),
            m <= n
    {
        if m % 2 == 0 {
            v.push('0');
        } else {
            v.push('1');
        }
        m = m / 2;
    }
    
    let mut i: usize = 0;
    let mut j: usize = v.len() - 1;
    
    while i < j
        invariant 
            i <= j,
            j < v.len(),
            ValidBitString(v@)
    {
        let temp = v[i];
        v.set(i, v[j]);
        v.set(j, temp);
        i = i + 1;
        if j > 0 {
            j = j - 1;
        }
    }
    
    proof {
        lemma_int2str_valid(n as nat);
        lemma_str2int_int2str(n as nat);
    }
    
    v
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
    if sy.len() == 0 {
        // This case shouldn't happen due to precondition sy@.len() > 0
        // But we handle it for completeness
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    
    let y_val = str2int_exec(sy);
    
    if y_val == 0 {
        // x^0 = 1, so result is 1 mod z
        let z_val = str2int_exec(sz);
        proof {
            lemma_exp_zero(Str2Int(sx@));
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        let result_val = 1 % z_val;
        let res = int2str_exec(result_val);
        proof {
            assert(Str2Int(res@) == result_val);
            assert(result_val == 1u64 % z_val);
            assert(z_val == Str2Int(sz@));
            assert(result_val as nat == 1nat % Str2Int(sz@));
            assert(result_val as nat == Exp_int(Str2Int(sx@), 0) % Str2Int(sz@));
        }
        return res;
    }
    
    // Recursive case: y > 0
    // We need to compute x^y mod z = (x * x^(y-1)) mod z
    
    // First compute y - 1
    let y_minus_1 = y_val - 1;
    let sy_minus_1 = int2str_exec(y_minus_1);
    
    // Recursive call to compute x^(y-1) mod z
    let recursive_result = ModExp(sx, &sy_minus_1, sz);
    
    // Now compute (x * recursive_result) mod z
    let x_val = str2int_exec(sx);
    let z_val = str2int_exec(sz);
    let rec_val = str2int_exec(&recursive_result);
    
    let x_mod = x_val % z_val;
    let product = (x_mod * rec_val) % z_val;
    
    let res = int2str_exec(product);
    
    // Prove correctness
    proof {
        assert(Str2Int(sy_minus_1@) == y_val - 1);
        assert(y_val == Str2Int(sy@));
        assert(Str2Int(recursive_result@) == Exp_int(Str2Int(sx@), (Str2Int(sy@) - 1) as nat) % Str2Int(sz@));
        
        lemma_exp_mod(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) == 
               ((Str2Int(sx@) % Str2Int(sz@)) * (Exp_int(Str2Int(sx@), (Str2Int(sy@) - 1) as nat) % Str2Int(sz@))) % Str2Int(sz@));
        
        assert(product == ((x_val % z_val) * rec_val) % z_val as int);
        assert(x_val == Str2Int(sx@));
        assert(z_val == Str2Int(sz@));
        assert(rec_val == Exp_int(Str2Int(sx@), (Str2Int(sy@) - 1) as nat) % Str2Int(sz@));
        assert(product == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        assert(Str2Int(res@) == product);
    }
    
    res
}
// </vc-code>

fn main() {}
}