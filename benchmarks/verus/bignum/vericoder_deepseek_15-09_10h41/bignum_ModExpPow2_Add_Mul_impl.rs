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

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
fn add_impl(s1: &[char], s2: &[char]) -> Vec<char> {
    /* code modified by LLM (iteration 5): Fixed function declaration syntax */
    let len = std::cmp::max(s1.len(), s2.len());
    let mut result = Vec::with_capacity(len + 1);
    let mut carry = 0;
    let mut i = 0;
    while i < len
        invariant
            0 <= i && i <= len,
            result@.len() == i,
            ValidBitString(result@),
            Str2Int(result@) + Exp_int(2, i as nat) * carry == (
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int))
            )
        decreases len - i
    {
        let bit1 = if i < s1.len() && s1[i] == '1' { 1 } else { 0 };
        let bit2 = if i < s2.len() && s2[i] == '1' { 1 } else { 0 };
        let sum = bit1 + bit2 + carry;
        carry = if sum > 1 { 1 } else { 0 };
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        i += 1;
    }
    if carry == 1 {
        result.push('1');
    }
    result
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed main function wrapper */
    add_impl(s1, s2)
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed main function wrapper */
    let len1 = s1.len();
    let len2 = s2.len();
    let mut result = vec!['0'; len1 + len2];
    let mut i = 0;
    while i < len2
        invariant
            0 <= i && i <= len2,
            result@.len() == len1 + len2,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, i as int))
        decreases len2 - i
    {
        if s2[len2 - 1 - i] == '1' {
            let mut temp = s1.to_vec();
            for _ in 0..i {
                temp.push('0');
            }
            result = Add(&result, &temp);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}
