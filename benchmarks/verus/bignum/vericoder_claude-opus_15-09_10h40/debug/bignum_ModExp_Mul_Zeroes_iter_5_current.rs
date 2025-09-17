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
/* helper modified by LLM (iteration 5): fixed lemmas and corrected int_to_str_exec */
proof fn lemma_exp_split(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == if y == 0 { 1nat % z } else { ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z }
{
    if y == 0 {
        assert(Exp_int(x, y) == 1);
        assert(Exp_int(x, y) % z == 1 % z);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert((x * Exp_int(x, (y - 1) as nat)) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z) by {
            vstd::calc::calc_mod::lemma_mod_mul_equivalent(x as int, Exp_int(x, (y - 1) as nat) as int, z as int);
        }
    }
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    vstd::calc::calc_mod::lemma_mod_mul_equivalent(a as int, b as int, m as int);
}

exec fn str_to_int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
        s@.len() <= 64,
    ensures res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@),
            result <= u64::MAX / 2,
        decreases s.len() - i
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    assert(s@.subrange(0, s@.len() as int) =~= s@);
    result
}

exec fn int_to_str_exec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    let orig_n = n;
    let mut curr_n = n;
    let mut result = Vec::<char>::new();
    if curr_n == 0 {
        result.push('0');
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 0);
        return result;
    }
    
    assert(orig_n as nat == curr_n as nat * Exp_int(2, 0) + 0) by {
        assert(Exp_int(2, 0) == 1);
    }
    assert(Str2Int(result@) == 0) by {
        assert(result@.len() == 0);
    }
    
    while curr_n > 0
        invariant
            ValidBitString(result@),
            curr_n as nat * Exp_int(2, result@.len() as nat) + Str2Int(result@) == orig_n as nat,
        decreases curr_n
    {
        let old_curr = curr_n;
        let old_len = result.len();
        let old_str2int = Str2Int(result@);
        
        if curr_n % 2 == 1 {
            result.push('1');
            assert(Str2Int(result@) == 2 * old_str2int + 1) by {
                assert(result@.subrange(0, old_len as int) =~= result@.subrange(0, result@.len() - 1));
            }
        } else {
            result.push('0');
            assert(Str2Int(result@) == 2 * old_str2int) by {
                assert(result@.subrange(0, old_len as int) =~= result@.subrange(0, result@.len() - 1));
            }
        }
        curr_n = curr_n / 2;
        
        assert(curr_n as nat * Exp_int(2, result@.len() as nat) + Str2Int(result@) == orig_n as nat) by {
            assert(result@.len() == old_len + 1);
            assert(Exp_int(2, result@.len() as nat) == 2 * Exp_int(2, old_len as nat));
            if old_curr % 2 == 1 {
                assert(old_curr as nat == 2 * curr_n + 1);
                assert(Str2Int(result@) == 2 * old_str2int + 1);
            } else {
                assert(old_curr as nat == 2 * curr_n);
                assert(Str2Int(result@) == 2 * old_str2int);
            }
        }
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed precondition issues and recursion structure */
    if sy@.len() <= 64 && sx@.len() <= 64 && sz@.len() <= 64 {
        if sy.len() == 1 && sy[0] == '0' {
            let mut res = Vec::<char>::new();
            res.push('1');
            assert(ValidBitString(res@));
            assert(Str2Int(res@) == 1);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            return res;
        }
        
        let x_val = str_to_int_exec(sx);
        let z_val = str_to_int_exec(sz);
        
        if sy.len() == 1 && sy[0] == '1' {
            let res_val = x_val % z_val;
            proof {
                assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
                lemma_exp_split(Str2Int(sx@), 1, z_val as nat);
            }
            return int_to_str_exec(res_val);
        }
        
        let mut sy_half = Vec::<char>::new();
        for i in 0..(sy.len() / 2)
            invariant
                0 <= i <= sy.len() / 2,
                sy_half@.len() == i,
                ValidBitString(sy_half@),
                forall|j: int| 0 <= j < i ==> sy_half@[j] == sy@[j],
        {
            sy_half.push(sy[i]);
        }
        
        let half_res = ModExp_Mul_Zeroes(sx, &sy_half, sz);
        let half_val = if half_res.len() <= 64 { str_to_int_exec(&half_res) } else { 0 };
        
        let mut result_val = if half_res.len() <= 64 { (half_val * half_val) % z_val } else { 0 };
        
        if sy[sy.len() - 1] == '1' {
            result_val = (result_val * (x_val % z_val)) % z_val;
        }
        
        proof {
            if half_res.len() <= 64 {
                lemma_exp_split(x_val as nat, Str2Int(sy@), z_val as nat);
                lemma_mod_mul(half_val as nat, half_val as nat, z_val as nat);
                if sy[sy.len() - 1] == '1' {
                    lemma_mod_mul(result_val as nat, x_val as nat, z_val as nat);
                }
            }
        }
        
        int_to_str_exec(result_val)
    } else {
        // Handle large inputs by simple recursion
        if sy[sy.len() - 1] == '0' {
            let mut sy_div2 = Vec::<char>::new();
            for i in 0..(sy.len() - 1)
                invariant
                    0 <= i <= sy.len() - 1,
                    sy_div2@.len() == i,
                    ValidBitString(sy_div2@),
                    forall|j: int| 0 <= j < i ==> sy_div2@[j] == sy@[j],
            {
                sy_div2.push(sy[i]);
            }
            let temp = ModExp_Mul_Zeroes(sx, &sy_div2, sz);
            let res = ModExp_Mul_Zeroes(&temp, &temp, sz);
            proof {
                lemma_exp_split(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
            }
            res
        } else {
            let mut sy_minus1 = Vec::<char>::new();
            for i in 0..(sy.len() - 1)
                invariant
                    0 <= i <= sy.len() - 1,
                    sy_minus1@.len() == i,
                    ValidBitString(sy_minus1@),
                    forall|j: int| 0 <= j < i ==> sy_minus1@[j] == sy@[j],
            {
                sy_minus1.push(sy[i]);
            }
            sy_minus1.push('0');
            let temp = ModExp_Mul_Zeroes(sx, &sy_minus1, sz);
            let res = ModExp_Mul_Zeroes(&temp, sx, sz);
            proof {
                lemma_exp_split(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
            }
            res
        }
    }
}
// </vc-code>

fn main() {}
}
