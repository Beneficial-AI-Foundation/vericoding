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

exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  assume(false);
  return Vec::<char>::new();
}

exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
{
  assume(false);
  return (Vec::<char>::new(), Vec::<char>::new());
}

exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
{
  assume(false);
  return Vec::<char>::new();
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat literal usage in CreatePowerOf2String */
spec fn IsPowerOf2(n: nat) -> bool
{
    exists |k: nat| n == Exp_int(2, k)
}

spec fn Log2Floor(n: nat) -> nat
    requires n > 0
{
    if n == 1 { 0 } else { 1 + Log2Floor(n / 2) }
}

spec fn FindPowerOf2Component(y: nat) -> nat
    requires y > 0
{
    if y % 2 == 0 { 1 + FindPowerOf2Component(y / 2) } else { 0 }
}

exec fn IsZero(s: &[char]) -> (res: bool)
    requires ValidBitString(s@)
    ensures res == (Str2Int(s@) == 0)
{
    s.len() == 0 || s.iter().all(|&c| c == '0')
}

exec fn CreatePowerOf2String(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
        Str2Int(res@) == Exp_int(2, n),
        res@.len() == n + 1
{
    let mut result: Vec<char> = Vec::new();
    let mut i: nat = 0nat;
    while i < n
        invariant
            i <= n,
            result.len() == i,
    {
        result.push('0');
        i = i + 1nat;
    }
    result.push('1');
    result
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
    /* code modified by LLM (iteration 5): fixed nat arithmetic in loop */
    if IsZero(sy) {
        return vec!['1'];
    }
    
    let mut current_base = sx.to_vec();
    let mut current_exp = sy.to_vec();
    let mut result = vec!['1'];
    
    while !IsZero(&current_exp)
        invariant
            ValidBitString(current_base@),
            ValidBitString(current_exp@),
            ValidBitString(result@),
            Str2Int(result@) * Exp_int(Str2Int(current_base@), Str2Int(current_exp@)) % Str2Int(sz@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@),
        decreases Str2Int(current_exp@)
    {
        if current_exp[current_exp.len() - 1] == '1' {
            let temp = result.clone();
            result = DivMod(&Add(&temp, &current_base), sz).1;
        }
        
        let temp_base = current_base.clone();
        current_base = DivMod(&Add(&temp_base, &temp_base), sz).1;
        
        let mut new_exp = Vec::new();
        for i in 0..current_exp.len() - 1 {
            new_exp.push(current_exp[i]);
        }
        current_exp = new_exp;
    }
    
    result
}
// </vc-code>

fn main() {}
}
