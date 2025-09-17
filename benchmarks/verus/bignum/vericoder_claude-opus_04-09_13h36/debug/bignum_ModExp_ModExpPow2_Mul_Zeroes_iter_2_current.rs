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
    } else if n == 1 {
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        lemma_int2str_valid(n / 2);
        assert(Int2Str(n) == s.push(if n % 2 == 0 { '0' } else { '1' }));
        assert(Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (if n % 2 == 1 { 1nat } else { 0nat }));
        assert(Str2Int(s) == n / 2);
        assert(2 * (n / 2) + (if n % 2 == 1 { 1nat } else { 0nat }) == n);
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
        return vec!['0'];
    }
    
    let mut result = Vec::<char>::new();
    let mut val = n;
    
    while val > 0
        invariant 
            val <= n,
            ValidBitString(result@),
            n == val + Str2Int(result@) * Exp_int(2, result@.len() as nat),
            forall |i: int| 0 <= i && i < result@.len() ==> #[trigger] result@[i] == Int2Str(n as nat)[i]
    {
        result.push(if val % 2 == 0 { '0' } else { '1' });
        val = val / 2;
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
            result == Str2Int(s@.subrange(0, i as int)),
            result < Exp_int(2, i as nat)
    {
        result = result * 2 + if s[i] == '1' { 1 } else { 0 };
        i = i + 1;
    }
    
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
    let x_val = str_to_int(sx);
    let y_val = str_to_int(sy);
    let z_val = str_to_int(sz);
    
    let mut result: u64 = 1;
    let mut base: u64 = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant
            z_val == Str2Int(sz@),
            z_val > 1,
            base < z_val,
            result < z_val,
            (result as nat) * Exp_int(base as nat, exp as nat) % (z_val as nat) == 
                Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
    {
        if exp % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    int_to_str(result)
}
// </vc-code>

fn main() {}
}