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
/* helper modified by LLM (iteration 2): Use u64 and usize for exec computation to avoid int/nat in exec code */
fn Str2IntExec(s: &[char]) -> u64
    requires
        ValidBitString(s@),
        s.len() <= 64,
    ensures
        Str2Int(s@) as u64 == result,
{
    let mut result: u64 = 0;
    let mut power: u64 = 1;
    let mut i: usize = s.len() - 1;
    while i >= 0
        invariant
            i < s.len(),
            0 <= power <= (1u64 << 64) - 1,
    {
        if s[i] == '1' {
            result = result.wrapping_add(power);
        }
        power = power.wrapping_mul(2);
        i -= 1;
    }
    result
}

fn Nat2BitsExecU64(n: u64) -> Vec<char>
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    let mut current: u64 = n;
    while current > 0 {
        let bit = if current % 2 == 1 { '1' } else { '0' };
        result.push(bit);
        current /= 2;
    }
    result.reverse();
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Use u64 for computations and new helper */
{
    let a_num = Str2IntExec(a);
    let b_num = Str2IntExec(b);
    let sum = a_num.wrapping_add(b_num);
    let bits = Nat2BitsExecU64(sum);
    bits
}
// </vc-code>

fn main() {}
}

