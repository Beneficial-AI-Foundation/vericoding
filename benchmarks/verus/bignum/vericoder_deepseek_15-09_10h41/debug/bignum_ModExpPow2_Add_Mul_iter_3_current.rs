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
    /* code modified by LLM (iteration 3): Fixed function signature and braces */
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
    /* code modified by LLM (iteration 3): Fixed function signature and braces */
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
            result = add_impl(&result, &temp);
        }
        i += 1;
    }
    result
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
    /* code modified by LLM (iteration 3): Fixed function signature and braces */
    let mut x = Str2Int(sx@) % Str2Int(sz@);
    let mut result = 1;
    let mut i = 0;
    while i < n as usize
        invariant
            0 <= i && i <= n as usize,
            result == Exp_int(Str2Int(sx@) % Str2Int(sz@), Str2Int(sy@.subrange(0, i as int))) % Str2Int(sz@)
        decreases n - i as int
    {
        if sy[i] == '1' {
            result = (result * x) % Str2Int(sz@);
        }
        x = (x * x) % Str2Int(sz@);
        i += 1;
    }
    let mut res_chars = Vec::<char>::new();
    let mut num = result;
    while num > 0
        invariant
            num >= 0,
            ValidBitString(res_chars@),
            Str2Int(res_chars@) == num
        decreases num
    {
        if num % 2 == 1 {
            res_chars.push('1');
        } else {
            res_chars.push('0');
        }
        num = num / 2;
    }
    res_chars.reverse();
    if res_chars.is_empty() {
        res_chars.push('0');
    }
    res_chars
}
// </vc-code>

fn main() {}
}
