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
exec fn str_to_int_exec(s: &[char]) -> (n: nat)
    requires ValidBitString(s@)
    ensures n == Str2Int(s@)
{
    let mut n: nat = 0;
    let mut i: nat = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            n == Str2Int(s@.subrange(0, i as int)),
    {
        n = n * 2;
        if s[i] == '1' {
            n = n + 1;
        }
        i = i + 1;
    }
    n
}

exec fn int_to_str_exec(n: nat) -> (v: Vec<char>)
    ensures ValidBitString(v@) && Str2Int(v@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    let mut digits: Vec<char> = Vec::new();
    let mut current: nat = n;
    while current > 0
        invariant
            current > 0 == (digits.len() > 0),
            n == current * (2 as nat).pow(digits.len() as nat) + Str2Int(digits@),
        decreases current
    {
        let bit = if current % 2 == 0 { '0' } else { '1' };
        digits.push(bit);
        current = current / 2;
    }
    digits.reverse();
    digits
}
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
    let m = str_to_int_exec(sz);
    let base_int = str_to_int_exec(sx);
    let base = base_int % m;
    let mut result = 1;
    let mut i = 0;
    while i < sy.len()
        invariant
            0 <= i <= sy.len(),
            result == Exp_int(base, Str2Int(sy@.subrange(0, i as int))) % m,
        decreases sy@.len() - i
    {
        result = (result * result) % m;
        if sy[i] == '1' {
            result = (result * base) % m;
        }
        i = i + 1;
    }
    let res = int_to_str_exec(result);
    res
}
// </vc-code>

fn main() {}
}


