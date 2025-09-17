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
/* helper modified by LLM (iteration 7): Add conversion functions for nat/int and ensure type safety */
proof fn lemma_str2int_len(s: Seq<char>) ensures s.len() as int >= 0 { }
proof fn lemma_nat_to_int(x: nat) ensures x as int >= 0 { }
proof fn lemma_sub_len_nat(a: nat, b: nat) requires a >= b ensures (a - b) as int >= 0 { }
ghost fn usize_to_nat(x: usize) -> nat { x as nat }
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
/* code modified by LLM (iteration 7): Fix nat/int conversion errors by using usize and proper type conversions */
{
    let n: usize = sy.len() - 1;
    let (mut result, mut base, mut exponent) = (Vec::new(), sx.to_vec(), sy.to_vec());
    
    while exponent.len() > 0
        invariant
            ValidBitString(result@),
            ValidBitString(base@),
            ValidBitString(exponent@),
            Str2Int(result@) == Exp_int(Str2Int(sx@), (Str2Int(sy@) - Str2Int(exponent@)) as nat) % Str2Int(sz@),
            exponent@.len() <= sy@.len()
        decreases exponent@.len()
    {
        let last_char = *exponent.last().unwrap();
        exponent.pop();
        
        if last_char == '1' {
            let temp = ModExpPow2(&base, &exponent, n as int, &sz);
            result = Add(&result, &temp);
            let (_, rem) = DivMod(&result, &sz);
            result = rem;
        }
        
        base = ModExpPow2(&base, &exponent, n as int, &sz);
        let (_, rem) = DivMod(&base, &sz);
        base = rem;
        n = n - 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
