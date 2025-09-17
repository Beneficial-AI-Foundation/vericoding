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
fn Str2IntExec(s: &[char]) -> int
    requires
        ValidBitString(s@),
{
    let mut result: int = 0;
    let mut power: int = 1;
    let mut i: int = s.len() as int - 1;
    while i >= 0
        invariant
            0 <= i && i < s.len() as int,
            power >= 1,
        decreases i
    {
        if s@[i] == '1' {
            result = result + power;
        }
        power = power * 2;
        i = i - 1;
    }
    return result;
}

fn Nat2BitsExec(n: nat) -> Vec<char>
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    let mut current: nat = n;
    while current > 0
        invariant
            current >= 0,
        decreases current
    {
        let bit = if current % 2 == 1 { '1' } else { '0' };
        result.push(bit);
        current = current / 2;
    }
    result.reverse();
    return result;
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let a_num = Str2IntExec(a);
    let b_num = Str2IntExec(b);
    let sum = a_num + b_num;
    let bits = Nat2BitsExec(sum as nat);
    return bits;
}
// </vc-code>

fn main() {}
}

