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
spec fn NatToSeq(n: nat) -> Seq<char>
    decreases n
    ensures
        Str2Int(NatToSeq(n)) == n,
        ValidBitString(NatToSeq(n))
{
    if n == 0 {
        Seq::empty()
    } else {
        let prev = NatToSeq(n / 2);
        prev + Seq::unit(if n % 2 == 1 { '1' } else { '0' })
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let m = Str2Int(sz@);
    let base = Str2Int(sx@) % m;
    let mut acc = 1 % m;
    let mut b = base;
    let mut e = Str2Int(sy@);

    while e > 0
        invariant
            m > 1,
            0 <= e,
        decreases e
    {
        if e % 2 == 1 {
            acc = (acc * b) % m;
        }
        b = (b * b) % m;
        e = e / 2;
    }

    let seq = NatToSeq(acc);
    let mut res = Vec::<char>::new();
    let mut i: int = 0;
    let len_i = seq.len() as int;
    while i < len_i
        invariant
            0 <= i && i <= len_i,
        decreases len_i - i
    {
        res.push(seq.index(i));
        i += 1;
    }

    res
}
// </vc-code>

fn main() {}
}
