
use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn power2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * power2((n - 1) as nat)
    }
}

spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

/* helper modified by LLM (iteration 2): Fixed type annotations in proof */
proof fn lemma_str2int_int2str(n: nat)
    ensures
        n == 0 ==> Int2Str(n) == seq![],
        n > 0 ==> ValidBitString(Int2Str(n)),
        n > 0 ==> Str2Int(Int2Str(n)) == n,
    decreases n
{
    if n == 0 {
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        assert(Int2Str(n) == s.push(if n % 2 == 0 { '0' } else { '1' }));
        if n / 2 == 0 {
            assert(s == seq![]);
            assert(Int2Str(n).len() == 1);
            if n % 2 == 0 {
                assert(Int2Str(n) == seq!['0']);
                assert(Str2Int(seq!['0']) == 0);
            } else {
                assert(Int2Str(n) == seq!['1']);
                assert(Str2Int(seq!['1']) == 1);
            }
        } else {
            assert(ValidBitString(s));
            assert(Str2Int(s) == n / 2);
            let result = Int2Str(n);
            assert(result.len() > 0);
            assert(result.subrange(0, result.len() as int - 1) == s);
            assert(Str2Int(result) == 2 * Str2Int(s) + if n % 2 == 0 { 0nat } else { 1nat });
            assert(Str2Int(result) == 2 * (n / 2) + n % 2);
            assert(2 * (n / 2) + n % 2 == n);
        }
    }
}

exec fn str2int_exec(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 64,
    ensures
        res as nat == Str2Int(s@),
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@),
            s@.len() <= 64,
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@.index(i as int)));
        i = i + 1;
    }
    assert(s@.subrange(0, i as int) == s@);
    result
}

exec fn int2str_exec(n: u64) -> (res: Vec<char>)
    ensures
        n == 0 ==> res@ == seq!['0'],
        n > 0 ==> ValidBitString(res@),
        n > 0 ==> Str2Int(res@) == n as nat,
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    
    let mut result = Vec::new();
    let mut num = n;
    
    while num > 0
        invariant
            num <= n,
            ValidBitString(result@),
            num > 0 || result@.len() > 0,
            n as nat == num as nat * power2(result@.len() as nat) + Str2Int(result@),
        decreases num
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    
    while i < j
        invariant
            i <= j,
            j < result.len(),
            i + j == result.len() - 1,
            ValidBitString(result@),
            Str2Int(result@) == n as nat,
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        if j > 0 {
            j = j - 1;
        }
    }
    
    proof {
        lemma_str2int_int2str(n as nat);
    }
    
    result
}

/* helper modified by LLM (iteration 2): Added exec version of power2 */
exec fn power2_exec(n: u32) -> (res: u64)
    requires n <= 63,
    ensures res == power2(n as nat),
{
    let mut result: u64 = 1;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            result == power2(i as nat),
            n <= 63,
    {
        result = result * 2;
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type errors and used exec version of power2 */
    let a_val = str2int_exec(a);
    let b_val = str2int_exec(b);
    
    let sum = a_val + b_val;
    let product = a_val * b_val;
    let div_result = if b_val != 0 { a_val / b_val } else { 0 };
    let mod_result = if b_val != 0 { a_val % b_val } else { a_val };
    
    let pow2_8 = power2_exec(8);
    let pow2_4 = power2_exec(4);
    let pow2_16 = power2_exec(16);
    
    let final_result = ((sum + product) * pow2_8 + div_result * pow2_4 + mod_result) % pow2_16;
    
    let res = int2str_exec(final_result);
    res
}
// </vc-code>

fn main() {}
}

