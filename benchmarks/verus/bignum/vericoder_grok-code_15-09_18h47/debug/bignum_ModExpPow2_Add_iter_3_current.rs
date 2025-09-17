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
{
/* code modified by LLM (iteration 2): Fixed type errors by using isize for indices instead of int, and usize for lengths where int cannot be used in exec. */
    let mut result = Vec::new();
    let len1 = s1.len() as isize;
    let len2 = s2.len() as isize;
    let mut i = len1 - 1;
    let mut j = len2 - 1;
    let mut carry = 0;
    while (i >= 0 || j >= 0 || carry > 0)
        invariant
            0 <= carry <= 1,
        decreases (((if i >= 0 { i } else { -1 }) as usize) + ((if j >= 0 { j } else { -1 }) as usize) + (carry as usize))
    {
        let a = if i >= 0 { if s1[i as usize] == '1' { 1 } else { 0 } } else { 0 };
        let b = if j >= 0 { if s2[j as usize] == '1' { 1 } else { 0 } } else { 0 };
        let sum = a + b + carry;
        carry = sum / 2;
        let bit = sum % 2;
        result.push(if bit == 1 { '1' } else { '0' });
        i = i - 1;
        j = j - 1;
    }
    // reverse result
    let len = result.len() as isize;
    let mut ii = 0 as isize;
    let mut jj = len - 1;
    while ii < jj
        invariant
            0 <= ii <= jj + 1 <= len,
        decreases (jj - ii)
    {
        let temp = result[ii as usize];
        result[ii as usize] = result[jj as usize];
        result[jj as usize] = temp;
        ii += 1;
        jj -= 1;
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
/* code modified by LLM (iteration 3): Fixed compilation error by changing sx@p as char to sx@[p] == '0' || sx@[p] == '1' in invariants, proper multi-line formatting, and fixed spec syntax in while invariant. */
proof {
    assert(forall |i: int| 0 <= i < sy@.len() ==> (sy@[i] == '0' || sy@[i] == '1'));
    assert(Str2Int(sy@) == 0 ||
           exists |k: int| 0 <= k <= n ==> Str2Int(sy@) == Exp_int(2, k as nat));
}
// compute base as Str2Int(sx@)
let mut base = 0usize;
for k in 0..sx.len()
    invariant
        forall |p: usize| 0 <= p < k ==> sx@[p] == '0' || sx@[p] == '1',
{
    base = base * 2 + (if sx[k] == '1' { 1 } else { 0 });
}
// compute is_zero for sy
let mut is_zero = true;
for k in 0..sy.len()
    invariant
        forall |p: usize| 0 <= p < k ==> sy@[p] == '0' || sy@[p] == '1',
{
    if sy[k] == '1' {
        is_zero = false;
    }
}
let exp: usize;
if is_zero {
    exp = 0;
} else {
    let mut e: usize = 1;
    let mut nn = n;
    while nn > 0
        invariant
            e == Exp_int(2, (n - nn) as nat),
        decreases (n - nn)
    {
        e = e * 2;
        nn -= 1;
    }
    exp = e;
}
// compute modz
let mut modz = 0usize;
for k in 0..sz.len()
    invariant
        forall |p: usize| 0 <= p < k ==> sz@[p] == '0' || sz@[p] == '1',
{
    modz = modz * 2 + (if sz[k] == '1' { 1 } else { 0 });
}
// compute res = base^exp % modz
let mut res = 1usize;
let mut e = exp;
let mut b = base;
while e > 0
    invariant res % modz * b % modz == b % modz,
    decreases e
{
    if e % 2 == 1 {
        res = (res * b) % modz;
    }
    b = (b * b) % modz;
    e = e / 2;
}
// now convert res to Vec<char>
if res == 0 {
    let mut vec = Vec::new();
    vec.push('0');
    return vec;
}
let mut result = Vec::<char>::new();
let mut r = res;
while r > 0
    decreases r
{
    result.push(if r % 2 == 1 { '1' } else { '0' });
    r = r / 2;
}
// reverse
let len = result.len() as isize;
let mut ii = 0 as isize;
let mut jj = len - 1;
while ii < jj
    decreases (jj - ii)
{
    let temp = result[ii as usize];
    result[ii as usize] = result[jj as usize];
    result[jj as usize] = temp;
    ii += 1;
    jj -= 1;
}
result
}
// </vc-code>

fn main() {}
}


