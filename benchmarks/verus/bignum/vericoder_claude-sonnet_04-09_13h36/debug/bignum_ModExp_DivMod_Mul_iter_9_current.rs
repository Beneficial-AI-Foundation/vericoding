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
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_one(x: nat)
    ensures Exp_int(x, 1) == x
{
    assert(Exp_int(x, 1) == x * Exp_int(x, 0));
    lemma_exp_zero(x);
    assert(Exp_int(x, 0) == 1);
    assert(x * 1 == x);
}

proof fn lemma_mod_identity(x: nat, m: nat)
    requires m > 1
    ensures x % m < m
{
}

spec fn Int2Str_helper(n: nat, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0 {
        if acc.len() == 0 { seq!['0'] } else { acc }
    } else {
        Int2Str_helper(n / 2, seq![if n % 2 == 1 { '1' } else { '0' }] + acc)
    }
}

spec fn Int2Str(n: nat) -> Seq<char> {
    Int2Str_helper(n, Seq::<char>::empty())
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    lemma_int2str_helper_valid(n, Seq::<char>::empty());
}

proof fn lemma_int2str_helper_valid(n: nat, acc: Seq<char>)
    requires ValidBitString(acc)
    ensures ValidBitString(Int2Str_helper(n, acc))
    decreases n
{
    if n == 0 {
        if acc.len() == 0 {
            assert(ValidBitString(seq!['0']));
        }
    } else {
        let new_acc = seq![if n % 2 == 1 { '1' } else { '0' }] + acc;
        assert(ValidBitString(new_acc));
        lemma_int2str_helper_valid(n / 2, new_acc);
    }
}

proof fn lemma_str2int_correctness(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    lemma_str2int_helper_correctness(n, Seq::<char>::empty());
}

proof fn lemma_str2int_helper_correctness(n: nat, acc: Seq<char>)
    requires ValidBitString(acc)
    ensures Str2Int(Int2Str_helper(n, acc)) == n * pow2(acc.len()) + Str2Int(acc)
    decreases n
{
    if n == 0 {
        if acc.len() == 0 {
            assert(Str2Int(seq!['0']) == 0);
        }
    } else {
        let new_acc = seq![if n % 2 == 1 { '1' } else { '0' }] + acc;
        lemma_str2int_helper_correctness(n / 2, new_acc);
    }
}

spec fn pow2(n: int) -> nat
    decreases n
{
    if n <= 0 { 1 } else { 2 * pow2(n - 1) }
}

exec fn int_to_bitvec(n: u32) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        proof {
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
        }
        result
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        let mut reconstructed: nat = 0;
        
        while temp > 0
            invariant 
                ValidBitString(result@),
                reconstructed + (temp as nat) * pow2(result@.len() as int) == n as nat,
                reconstructed == Str2Int(result@)
            decreases temp
        {
            let bit = if temp % 2 == 1 { '1' } else { '0' };
            result.insert(0, bit);
            
            proof {
                if temp % 2 == 1 {
                    reconstructed = reconstructed + pow2(result@.len() as int - 1);
                }
                assert(ValidBitString(result@));
            }
            
            temp = temp / 2;
        }
        
        proof {
            assert(reconstructed == n as nat);
            assert(Str2Int(result@) == n as nat);
        }
        
        result
    }
}

exec fn bitvec_to_nat(bits: &[char]) -> (res: u32)
    requires ValidBitString(bits@)
    ensures res as nat == Str2Int(bits@)
{
    let mut result: u64 = 0;
    let mut i = 0;
    
    while i < bits.len()
        invariant 
            0 <= i <= bits.len(),
            result as nat == Str2Int(bits@.subrange(0, i as int)),
            result < pow2(32)
        decreases bits.len() - i
    {
        result = result * 2;
        if bits[i] == '1' {
            result = result + 1;
        }
        
        proof {
            assert(result as nat == Str2Int(bits@.subrange(0, (i + 1) as int)));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(bits@.subrange(0, bits@.len() as int) == bits@);
        assert(result as nat == Str2Int(bits@));
    }
    
    result as u32
}

exec fn mod_exp(base: u32, exp: u32, modulus: u32) -> (res: u32)
    requires modulus > 1
    ensures res as nat == Exp_int(base as nat, exp as nat) % modulus as nat
{
    if exp == 0 {
        proof {
            lemma_exp_zero(base as nat);
            assert(Exp_int(base as nat, 0) == 1);
            assert(1 % modulus as nat == 1);
        }
        1
    } else {
        let mut result: u64 = 1;
        let mut base_pow: u64 = (base % modulus) as u64;
        let mut exp_remaining = exp;
        
        while exp_remaining > 0
            invariant 
                modulus > 1,
                result < modulus as u64,
                base_pow < modulus as u64,
                (result as nat * Exp_int(base_pow as nat, exp_remaining as nat)) % modulus as nat == Exp_int(base as nat, exp as nat) % modulus as nat
            decreases exp_remaining
        {
            if exp_remaining % 2 == 1 {
                result = (result * base_pow) % modulus as u64;
            }
            base_pow = (base_pow * base_pow) % modulus as u64;
            exp_remaining = exp_remaining / 2;
            
            proof {
                assert(result < modulus as u64);
                assert(base_pow < modulus as u64);
            }
        }
        
        proof {
            assert(exp_remaining == 0);
            lemma_exp_zero(base_pow as nat);
            assert(Exp_int(base_pow as nat, 0) == 1);
            assert((result as nat * 1) % modulus as nat == result as nat % modulus as nat);
            assert(result as nat % modulus as nat == result as nat);
        }
        
        result as u32
    }
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
    let x_val = bitvec_to_nat(sx);
    let y_val = bitvec_to_nat(sy);
    let z_val = bitvec_to_nat(sz);
    
    proof {
        assert(x_val as nat == Str2Int(sx@));
        assert(y_val as nat == Str2Int(sy@));
        assert(z_val as nat == Str2Int(sz@));
    }
    
    if y_val == 0 {
        let mut result = Vec::new();
        result.push('1');
        
        proof {
            assert(ValidBitString(result@));
            lemma_exp_zero(x_val as nat);
            assert(Exp_int(x_val as nat, 0) == 1);
            assert(Str2Int(result@) == 1);
            assert(1 % z_val as nat == 1);
        }
        
        return result;
    }
    
    let result_val = mod_exp(x_val, y_val, z_val);
    
    proof {
        assert(result_val as nat == Exp_int(x_val as nat, y_val as nat) % z_val as nat);
        assert(result_val as nat == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    let result = int_to_bitvec(result_val);
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == result_val as nat);
        assert(Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    result
}
// </vc-code>

fn main() {}
}