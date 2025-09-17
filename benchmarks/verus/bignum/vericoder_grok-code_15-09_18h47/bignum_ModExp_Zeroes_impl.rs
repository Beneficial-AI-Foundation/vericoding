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

// <vc-helpers>
/* helpers modified by LLM (iteration 2): Fixed type mismatches in Int2Str by using intermediate int casts to avoid subtraction resulting in int */
spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else if (n as int) % 2 == 0 {
        Int2Str(n / 2).push('0')
    } else {
        let half_minus = (((n as int) - 1) / 2) as nat;
        Int2Str(half_minus).push('1')
    }
}

spec fn ToBinary(n: nat) -> Seq<char>
{
    if n == 0 {
        seq!['0']
    } else {
        Int2Str(n)
    }
}

proof fn Int2Str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n == 0 {
    } else {
        Int2Str_valid(n / 2);
    }
}

proof fn ToBinary_valid(n: nat)
    ensures ValidBitString(ToBinary(n))
{
    Int2Str_valid(n);
}

proof fn Int2Str_correct(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
    } else {
        let s = Int2Str(n / 2);
        if n % 2 == 0 {
            assert(Str2Int(s.push('0')) == 2 * Str2Int(s));
        } else {
            assert(Str2Int(s.push('1')) == 2 * Str2Int(s) + 1);
        }
        Int2Str_correct(n / 2);
    }
}

proof fn ToBinary_correct(n: nat)
    ensures Str2Int(ToBinary(n)) == n
{
    if n == 0 {
    } else {
        Int2Str_correct(n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): Fixed number literal suffix, variable types, and loop indices to use usize for compatibility with vector lengths */
    let x_init: nat = (Str2Int(sx@) % Str2Int(sz@)) as nat;
    let mut x: nat = x_init;
    let mut res: nat = 1;
    let mut i: usize = 0;

    while i < (sy@.len() as usize)
        invariant
            true,
        decreases (sy@.len() as usize - i)
    {
        let bit = sy@[i as int];
        if bit == '1' {
            res = ((res as int) * (x as int) % (Str2Int(sz@) as int)) as nat;
        }
        x = ((x as int) * (x as int) % (Str2Int(sz@) as int)) as nat;
        i += 1;
    }

    let bin_res = ToBinary(res);
    let mut vec_res = Vec::with_capacity(bin_res.len() as usize);
    let mut j: usize = 0;
    while j < (bin_res.len() as usize)
        invariant
            true,
        decreases (bin_res.len() as usize - j)
    {
        vec_res.push(bin_res[j as int]);
        j += 1;
    }

    vec_res
}
// </vc-code>

fn main() {}
}
