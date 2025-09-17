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
    if n == 0 {
    } else if n == 1 {
    } else {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
    } else if n == 1 {
    } else {
        lemma_str2int_int2str(n / 2);
        assert(Int2Str(n) == Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' }));
        let s = Int2Str(n / 2);
        assert(Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (if n % 2 == 0 { 0 } else { 1 }));
        assert(Str2Int(s) == n / 2);
        assert(2 * (n / 2) + (if n % 2 == 0 { 0 } else { 1 }) == n);
    }
}

exec fn nat_to_vec(n: u64) -> (v: Vec<char>)
    ensures ValidBitString(v@), Str2Int(v@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        proof {
            assert(v@ == seq!['0']);
            assert(Str2Int(v@) == 0);
        }
        return v;
    } else if n == 1 {
        let mut v = Vec::new();
        v.push('1');
        proof {
            assert(v@ == seq!['1']);
            assert(Str2Int(v@) == 1);
        }
        return v;
    } else {
        let mut v = nat_to_vec(n / 2);
        if n % 2 == 0 {
            v.push('0');
        } else {
            v.push('1');
        }
        proof {
            assert(v@ == Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' }));
            lemma_int2str_valid(n);
            lemma_str2int_int2str(n);
        }
        v
    }
}

exec fn str_to_nat(s: &[char]) -> (n: u64)
    requires ValidBitString(s@), Str2Int(s@) < 0x10000000000000000
    ensures n == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        return 0;
    } else {
        let prefix = str_to_nat(&s[..s.len() - 1]);
        let last = if s[s.len() - 1] == '1' { 1u64 } else { 0u64 };
        proof {
            assert(s@.subrange(0, s@.len() - 1) == s[..s.len() - 1]@);
        }
        2 * prefix + last
    }
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
    if sy.len() == 0 {
        // This case shouldn't happen due to precondition sy@.len() > 0
        // But we need to handle it for totality
        return Vec::new();
    }
    
    // Base case: if y is "1", return x % z
    if sy.len() == 1 && sy[0] == '1' {
        let x_val = str_to_nat(sx);
        let z_val = str_to_nat(sz);
        let result_val = x_val % z_val;
        
        proof {
            assert(Str2Int(sy@) == 1);
            assert(Exp_int(x_val, 1) == x_val);
        }
        
        return nat_to_vec(result_val);
    }
    
    // Recursive case: compute x^(y/2) first
    let mut sy_half = Vec::new();
    let mut i: usize = 0;
    
    // Compute y/2 by right-shifting the bit string
    while i < sy.len() - 1
        invariant
            i <= sy.len() - 1,
            sy_half@ == sy@.subrange(0, i as int),
            ValidBitString(sy_half@),
    {
        sy_half.push(sy[i]);
        i = i + 1;
    }
    
    // Recursive call: compute x^(y/2) % z
    let half_result = ModExp_ModExpPow2_Mul_Zeroes(&sx, &sy_half, &sz);
    
    // Square the result: (x^(y/2))^2 % z
    let half_val = str_to_nat(&half_result);
    let z_val = str_to_nat(sz);
    let squared = (half_val * half_val) % z_val;
    
    // If y is odd, multiply by x one more time
    let result_val = if sy[sy.len() - 1] == '1' {
        let x_val = str_to_nat(sx);
        (squared * x_val) % z_val
    } else {
        squared
    };
    
    proof {
        let y_val = Str2Int(sy@);
        let x_val = Str2Int(sx@);
        
        assert(y_val > 0) by {
            assert(sy@.len() > 0);
        }
        
        if sy[sy.len() - 1] == '1' {
            assert(y_val % 2 == 1);
            assert(Exp_int(x_val, y_val) == x_val * Exp_int(x_val, (y_val - 1) as nat));
            assert((y_val - 1) / 2 == Str2Int(sy_half@));
        } else {
            assert(y_val % 2 == 0);
            assert(y_val / 2 == Str2Int(sy_half@));
        }
    }
    
    nat_to_vec(result_val)
}
// </vc-code>

fn main() {}
}