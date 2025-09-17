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
    } else {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        assert(Int2Str(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else if n == 1 {
        assert(Int2Str(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        lemma_int2str_valid(n / 2);
        let bit = if n % 2 == 0 { '0' } else { '1' };
        assert(Int2Str(n) == s.push(bit));
        assert(Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s) == n / 2);
        assert(2 * (n / 2) + (if n % 2 == 1 { 1nat } else { 0nat }) == n) by {
            if n % 2 == 0 {
                assert(n == 2 * (n / 2));
            } else {
                assert(n == 2 * (n / 2) + 1);
            }
        }
    }
}

proof fn lemma_str2int_subrange(s: Seq<char>, i: int)
    requires 0 <= i <= s.len(), ValidBitString(s)
    ensures Str2Int(s.subrange(0, i)) <= Str2Int(s)
    decreases s.len() - i
{
    if i == s.len() {
    } else {
        lemma_str2int_subrange(s.subrange(0, s.len() - 1), i);
        assert(s.subrange(0, i) == s.subrange(0, s.len() - 1).subrange(0, i));
    }
}

exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    proof { 
        lemma_int2str_valid(n as nat);
        lemma_str2int_int2str(n as nat);
    }
    
    if n == 0 {
        proof {
            assert(Str2Int(seq!['0']) == 0);
        }
        return vec!['0'];
    }
    
    let mut result = Vec::<char>::new();
    let mut val = n;
    
    while val > 0
        invariant 
            val <= n,
            ValidBitString(result@),
            result@.len() <= 64,
            if result@.len() == 0 {
                val == n
            } else {
                n == val * Exp_int(2, result@.len() as nat) + Str2Int(result@.subrange(0, result@.len())),
                forall |i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] == if ((n / Exp_int(2, i as nat)) % 2) == 0 { '0' } else { '1' }
            }
        decreases val
    {
        let old_result = result;
        let old_val = val;
        result.push(if val % 2 == 0 { '0' } else { '1' });
        val = val / 2;
        
        proof {
            if old_result@.len() == 0 {
                assert(Str2Int(result@.subrange(0, 1)) == if n % 2 == 0 { 0 } else { 1 });
                assert(n == val * 2 + (if n % 2 == 0 { 0 } else { 1 }));
            }
            assert(forall |i: int| 0 <= i < result@.len() ==> result@[i] == if ((n / Exp_int(2, i as nat)) % 2) == 0 { '0' } else { '1' });
        }
    }
    
    proof {
        assert(val == 0);
        assert(n == Str2Int(result@));
    }
    
    result
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 0x10000000000000000
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int)),
            result <= Str2Int(s@),
            Str2Int(s@) < 0x10000000000000000
        decreases s.len() - i
    {
        proof {
            lemma_str2int_subrange(s@, (i + 1) as int);
            assert(Str2Int(s@.subrange(0, (i + 1) as int)) <= Str2Int(s@));
            assert(Str2Int(s@.subrange(0, (i + 1) as int)) == 2 * result + if s[i] == '1' { 1 } else { 0 });
            assert(2 * result + if s[i] == '1' { 1 } else { 0 } < 0x10000000000000000);
        }
        result = result * 2 + if s[i] == '1' { 1 } else { 0 };
        i = i + 1;
    }
    
    assert(s@.subrange(0, s@.len() as int) == s@);
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    proof {
        assert(Str2Int(sx@) < Exp_int(2, 64));
        assert(Str2Int(sy@) < Exp_int(2, 64));
        assert(Str2Int(sz@) < Exp_int(2, 64));
    }
    
    let x_val = str_to_int(sx);
    let y_val = str_to_int(sy);
    let z_val = str_to_int(sz);
    
    let mut result: u64 = 1;
    let mut base: u64 = x_val % z_val;
    let mut exp = y_val;
    
    proof {
        assert(z_val == Str2Int(sz@));
        assert(base == x_val % z_val);
        assert((result as nat) * Exp_int(base as nat, exp as nat) % (z_val as nat) == 
            Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    while exp > 0
        invariant
            ValidBitString(sz@),
            z_val == Str2Int(sz@),
            z_val > 1,
            base < z_val,
            result < z_val,
            (result as nat) * Exp_int(base as nat, exp as nat) % (z_val as nat) == 
                Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
        decreases exp
    {
        if exp % 2 == 1 {
            proof {
                assert(result * base < 0x10000000000000000) by {
                    assert(result < z_val);
                    assert(base < z_val);
                    assert(z_val < 0x10000000000000000);
                }
            }
            result = (result * base) % z_val;
        }
        proof {
            assert(base * base < 0x10000000000000000) by {
                assert(base < z_val);
                assert(z_val < 0x10000000000000000);
            }
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    proof {
        assert(exp == 0);
        assert(Exp_int(base as nat, 0) == 1);
        assert(result == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    int_to_str(result)
}
// </vc-code>

fn main() {}
}