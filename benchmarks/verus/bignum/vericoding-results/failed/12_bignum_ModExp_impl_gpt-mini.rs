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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
fn nat_mod(a: nat, m: nat) -> nat { a % m }
spec fn is_valid_bitstring(s: Seq<char>) -> bool { ValidBitString(s) }
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let m: nat = Str2Int(sz@);
    let mut base: nat = Str2Int(sx@) % m;
    let len = sy@.len() as int;
    let mut res_int: nat = 1 % m;
    let mut b: nat = base;
    let mut i: int = 0;
    while i < len
        invariant
            i >= 0,
        decreases
            len - i
    {
        let idx = (len - 1 - i) as int;
        if sy@.index(idx) == '1' {
            res_int = (res_int * b) % m;
        }
        b = (b * b) % m;
        i = i + 1;
    }
    let mut v = Vec::<char>::new();
    if res_int == 0 {
        v.push('0');
        return v;
    }
    let mut t: nat = res_int;
    let mut bits = Vec::<char>::new();
    while t > 0
        invariant
            t >= 0,
        decreases
            t
    {
        if t % 2 == 1 {
            bits.push('1');
        } else {
            bits.push('0');
        }
        t = t / 2;
    }
    let mut res = Vec::<char>::new();
    let mut j: int = bits.len() as int - 1;
    while j >= 0
        invariant
            j >= -1,
        decreases
            j + 1
    {
        res.push(bits[j as usize]);
        j = j - 1;
    }
    res
}
// </vc-code>

fn main() {}
}


