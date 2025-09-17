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
spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else if n % 2 == 0 {
        Int2Str(n / 2).push('0')
    } else {
        Int2Str((n - 1) / 2).push('1')
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
    let mut x = Str2Int(sx@) % Str2Int(sz@);
    let mut res = 1nat;
    let mut i = 0;

    while i < sy@.len()
        invariant
            true,
        decreases sy@.len() - i
    {
        let bit = sy@[i];
        if bit == '1' {
            res = (res * x) % Str2Int(sz@);
        }
        x = (x * x) % Str2Int(sz@);
        i += 1;
    }

    let bin_res = ToBinary(res);
    let mut vec_res = Vec::with_capacity(bin_res.len());
    let mut j = 0;
    while j < bin_res.len()
        invariant
            true,
        decreases bin_res.len() - j
    {
        vec_res.push(bin_res[j]);
        j += 1;
    }

    vec_res
}
// </vc-code>

fn main() {}
}
