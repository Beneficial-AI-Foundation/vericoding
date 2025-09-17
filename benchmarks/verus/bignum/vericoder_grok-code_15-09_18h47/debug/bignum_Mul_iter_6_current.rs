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
spec fn power(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 }
    else { base * power(base, (exp as int - 1) as nat) }
}

/* helper modified by LLM (iteration 4): Fixed type mismatch by casting exp -1 back to nat. */
fn shift_left(v: &[char], n: usize) -> (result: Vec<char>)
    requires ValidBitString(v@)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(v@) * power(2, n as nat)
{
    let mut shifted = Vec::new();
    shifted.extend_from_slice(v);
    for _ in 0..n {
        shifted.push('0');
    }
    shifted
}

/* helper modified by LLM (iteration 6): Modified loop order to avoid reverse() call, which causes compilation error. */
fn add_binary(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(a@) + Str2Int(b@)
{
    let mut temp = Vec::new();
    let mut carry = false;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    for i in (0..max_len).rev() {
        let pos = i;
        let bit1 = pos < a.len() && a[a.len() - 1 - pos as usize] == '1';
        let bit2 = pos < b.len() && b[b.len() - 1 - pos as usize] == '1';
        let sum = bit1 as u8 + bit2 as u8 + carry as u8;
        let bit = sum % 2 != 0;
        carry = sum >= 2;
        temp.push(if bit { '1' } else { '0' });
    }
    if carry {
        temp.push('1');
    }
    temp
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implementing the binary multiplication by shifting and adding for each bit in s2. */
{
    let mut r = Vec::new();
    for i in 0..s2.len() {
        if s2[s2.len() - 1 - i] == '1' {
            let shifted = shift_left(s1, i);
            r = add_binary(&r, &shifted);
        }
    }
    r
}
// </vc-code>

fn main() {}
}


