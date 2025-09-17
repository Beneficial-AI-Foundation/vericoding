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
/* helper modified by LLM (iteration 5): convert nat to bit sequence (MSB..LSB, last char is LSB) */
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
/* code modified by LLM (iteration 5): modular exponentiation and convert to bit-vector (MSB..LSB) */
{
    let m: nat = Str2Int(sz@);
    let mut acc: nat = 1 % m;
    let mut b: nat = Str2Int(sx@) % m;
    let mut e: nat = Str2Int(sy@);

    while e > 0
        invariant
            m > 1,
            acc < m,
            b < m,
        decreases e
    {
        if e % 2 == 1 {
            acc = (acc * b) % m;
        }
        b = (b * b) % m;
        e = e / 2;
    }

    let mut tmp = Vec::<char>::new();
    if acc == 0 {
        // represent zero as empty sequence per Str2Int definition
    } else {
        let mut x: nat = acc;
        while x > 0
            invariant
                x <= acc,
            decreases x
        {
            if x % 2 == 1 {
                tmp.push('1');
            } else {
                tmp.push('0');
            }
            x = x / 2;
        }
    }

    let mut res = Vec::<char>::new();
    let len_tmp: int = tmp.len() as int;
    let mut j: int = 0;
    while j < len_tmp
        invariant
            0 <= j && j <= len_tmp,
        decreases len_tmp - j
    {
        let idx: usize = (len_tmp - 1 - j) as usize;
        res.push(tmp[idx]);
        j += 1;
    }

    res
}
// </vc-code>

fn main() {}
}
