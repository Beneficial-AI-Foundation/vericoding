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
/* helper modified by LLM (iteration 6): Fixed type annotation for empty sequence comparison */
proof fn lemma_exp_int_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_int_succ(x: nat, y: nat)
    ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_exp_int_split(x: nat, y1: nat, y2: nat)
    ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
    decreases y2
{
    if y2 == 0 {
        assert(Exp_int(x, y1 + 0) == Exp_int(x, y1));
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x, y1) * 1 == Exp_int(x, y1));
    } else {
        assert(Exp_int(x, y1 + y2) == x * Exp_int(x, ((y1 + y2) - 1) as nat));
        lemma_exp_int_split(x, y1, (y2 - 1) as nat);
        assert(Exp_int(x, y1 + (y2 - 1) as nat) == Exp_int(x, y1) * Exp_int(x, (y2 - 1) as nat));
        assert(Exp_int(x, y2) == x * Exp_int(x, (y2 - 1) as nat));
        assert(x * Exp_int(x, y1) * Exp_int(x, (y2 - 1) as nat) == Exp_int(x, y1) * x * Exp_int(x, (y2 - 1) as nat));
    }
}

spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        Int2Str(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n != 0 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        let empty_seq: Seq<char> = seq![];
        assert(Int2Str(0) == empty_seq);
        assert(Str2Int(empty_seq) == 0);
    } else {
        let s = Int2Str(n / 2);
        lemma_str2int_int2str(n / 2);
        assert(Str2Int(s) == n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        let full = s.push(bit);
        assert(full == Int2Str(n));
        assert(full.len() == s.len() + 1);
        assert(full.subrange(0, full.len() as int - 1) == s);
        assert(full.index(full.len() as int - 1) == bit);
        assert(Str2Int(full) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }));
        assert(Str2Int(full) == 2 * (n / 2) + n % 2);
        assert(2 * (n / 2) + n % 2 == n);
    }
}

exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + num * Exp_int(2, result@.len() as nat) == n,
        decreases num
    {
        let bit = if num % 2 == 1 { '1' } else { '0' };
        result.push(bit);
        num = num / 2;
    }
    
    proof {
        lemma_int2str_valid(n as nat);
        lemma_str2int_int2str(n as nat);
    }
    
    result
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
             Str2Int(s@) < u64::MAX
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            Str2Int(s@.subrange(0, i as int)) < u64::MAX,
        decreases s.len() - i
    {
        let bit_val: u64 = if s[i] == '1' { 1 } else { 0 };
        result = result * 2 + bit_val;
        i = i + 1;
    }
    
    assert(s@.subrange(0, s@.len() as int) == s@);
    result
}

exec fn mod_exp(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1,
             base < modulus
    ensures res == Exp_int(base as nat, exp as nat) % (modulus as nat),
            res < modulus
{
    let mut result: u64 = 1;
    let mut b = base;
    let mut e = exp;
    
    while e > 0
        invariant
            modulus > 1,
            result < modulus,
            b < modulus,
            (result as nat * Exp_int(b as nat, e as nat)) % (modulus as nat) == Exp_int(base as nat, exp as nat) % (modulus as nat),
        decreases e
    {
        if e % 2 == 1 {
            result = (result * b) % modulus;
        }
        b = (b * b) % modulus;
        e = e / 2;
        
        proof {
            if e > 0 {
                lemma_exp_int_split(b as nat, 1, (e - 1) as nat);
            }
        }
    }
    
    proof {
        assert(e == 0);
        assert(Exp_int(b as nat, 0) == 1);
        assert((result as nat * 1) % (modulus as nat) == Exp_int(base as nat, exp as nat) % (modulus as nat));
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): Implementation using helper functions */
    let x_int = str_to_int(sx);
    let y_int = str_to_int(sy);
    let z_int = str_to_int(sz);
    
    let result_int = mod_exp(x_int % z_int, y_int, z_int);
    
    let result = int_to_str(result_int);
    
    proof {
        lemma_int2str_valid(result_int as nat);
        lemma_str2int_int2str(result_int as nat);
    }
    
    result
}
// </vc-code>

fn main() {}
}
