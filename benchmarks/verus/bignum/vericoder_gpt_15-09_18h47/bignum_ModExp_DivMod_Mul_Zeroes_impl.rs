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
/* helper modified by LLM (iteration 2): provide Int2Bits and supporting lemmas for validity and round-trip with Str2Int */
spec fn Int2Bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { Seq::<char>::empty() } else { Int2Bits(n / 2).push(if n % 2 == 1 { '1' } else { '0' }) }
}

/* helper modified by LLM (iteration 2): lemma showing pushing a bit preserves ValidBitString */
proof fn lemma_valid_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
}

/* helper modified by LLM (iteration 2): prove Int2Bits produces a valid bit string */
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

/* helper modified by LLM (iteration 2): arithmetic facts about division and modulo 2 */
proof fn lemma_mod2_props(n: nat)
    ensures
        n == 2 * (n / 2) + (n % 2),
        n % 2 == 0 || n % 2 == 1,
{
}

/* helper modified by LLM (iteration 2): prove Str2Int(Int2Bits(n)) == n by recursion */
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
    /* code modified by LLM (iteration 2): construct result via Int2Bits and convert with Vec::from; added proof calls */
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let m = Str2Int(sz@);
    let val = Exp_int(base, exp) % m;
    let bs = Int2Bits(val);
    proof {
        lemma_Int2Bits_valid(val);
        lemma_Str2Int_Int2Bits(val);
    }
    let res_vec: Vec<char> = Vec::<char>::from(bs);
    res_vec
}
// </vc-code>

fn main() {}
}
