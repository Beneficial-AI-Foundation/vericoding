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
exec fn str_to_nat(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
{
    let mut result: nat = 0nat;
    let seq = s@;
    for i in 0..(seq.len() as int)
        invariant result == Str2Int(seq.subrange(0, i))
    {
        result = 2 * result + (if seq[i] == '1' { 1nat } else { 0nat });
    }
    result
}

exec fn mod_exp(x: nat, y: nat, m: nat) -> nat
    requires m > 0
    ensures result == Exp_int(x, y) % m
    decreases y
{
    if y == 0 {
        if m == 1 { 0 } else { 1 }
    } else {
        let r = mod_exp(x, y - 1, m);
        (r * x) % m
    }
}

exec fn nat_to_str(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@)
        && Str2Int(result@) == n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut bits: Vec<char> = Vec::<char>::new();
        let mut current: nat = n;
        while current > 0
            invariant current >= 0
            decreases current
        {
            if current % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            current = current / 2;
        }
        bits.reverse();
        bits
    }
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
    /* code modified by LLM (iteration 2): implement modular exponentiation using helpers */
    let x_nat = str_to_nat(sx);
    let y_nat = str_to_nat(sy);
    let z_nat = str_to_nat(sz);
    let result_nat = mod_exp(x_nat, y_nat, z_nat);
    let res = nat_to_str(result_nat);
    res
}
// </vc-code>

fn main() {}
}


