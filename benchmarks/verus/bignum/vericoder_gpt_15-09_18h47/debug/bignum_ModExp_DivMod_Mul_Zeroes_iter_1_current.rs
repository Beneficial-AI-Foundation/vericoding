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
spec fn Int2Bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { Seq::<char>::empty() } else { Int2Bits(n / 2).push(if n % 2 == 1 { '1' } else { '0' }) }
}

proof fn lemma_valid_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
}

proof fn lemma_Int2Bits_valid(n: nat)
    ensures
        ValidBitString(Int2Bits(n)),
    decreases n
{
    if n == 0 {
    } else {
        lemma_Int2Bits_valid(n / 2);
        lemma_valid_push(Int2Bits(n / 2), if n % 2 == 1 { '1' } else { '0' });
    }
}

proof fn lemma_mod2_props(n: nat)
    ensures
        n == 2 * (n / 2) + (n % 2),
        n % 2 == 0 || n % 2 == 1,
{
}

proof fn lemma_Str2Int_Int2Bits(n: nat)
    ensures
        Str2Int(Int2Bits(n)) == n,
    decreases n
{
    if n == 0 {
    } else {
        lemma_Int2Bits_valid(n / 2);
        lemma_Str2Int_Int2Bits(n / 2);
        lemma_mod2_props(n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let bs = Int2Bits(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    proof {
        lemma_Int2Bits_valid(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        lemma_Str2Int_Int2Bits(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    let res_vec = Vec::<char>::from_seq(bs);
    res_vec
}
// </vc-code>

fn main() {}
}
