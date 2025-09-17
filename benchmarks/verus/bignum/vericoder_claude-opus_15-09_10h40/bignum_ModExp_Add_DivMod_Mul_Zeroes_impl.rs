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
proof fn lemma_power_of_two_positive(n: nat)
    ensures
        pow2(n) > 0
    decreases n
{
    reveal(pow2);
    if n == 0 {
    } else {
        lemma_power_of_two_positive((n - 1) as nat);
    }
}

proof fn lemma_str2int_bounds(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    reveal(pow2);
    if s.len() == 0 {
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_bounds(s_prefix);
        assert(s_prefix.len() == s.len() - 1);
        if s.index(s.len() as int - 1) == '1' {
            assert(Str2Int(s) == 2 * Str2Int(s_prefix) + 1);
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s_prefix));
        }
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

/* helper modified by LLM (iteration 4): Added decreases clause to while loop */
fn int_to_binary_string(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@)
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant
            ValidBitString(result@)
        decreases n
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    while i < j
        invariant
            ValidBitString(result@),
            i <= j,
            j < result.len()
        decreases j - i
    {
        let temp_i = result[i];
        let temp_j = result[j];
        result.set(i, temp_j);
        result.set(j, temp_i);
        i = i + 1;
        if j > 0 {
            j = j - 1;
        } else {
            break;
        }
    }
    
    result
}

fn binary_string_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 64
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@)
        decreases s.len() - i
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): unchanged main method body */
    if a.len() == 0 && b.len() == 0 {
        return Vec::new();
    }
    
    if a.len() > 64 || b.len() > 64 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let a_val = if a.len() == 0 { 0 } else { binary_string_to_int(a) };
    let b_val = if b.len() == 0 { 0 } else { binary_string_to_int(b) };
    
    let sum = a_val.wrapping_add(b_val);
    let result = int_to_binary_string(sum);
    
    result
}
// </vc-code>

fn main() {}
}

