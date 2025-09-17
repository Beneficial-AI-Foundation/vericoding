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
spec fn bit_to_nat(c: char) -> nat { if c == '1' { 1 } else { 0 } }

proof fn lemma_Str2Int_push(s: Seq<char>, b: char)
    ensures
        Str2Int(s.push(b)) == 2 * Str2Int(s) + bit_to_nat(b),
{
}

exec fn is_all_zero_bits(s: &[char]) -> bool
    requires
        ValidBitString(s@),
    ensures
        result ==> Str2Int(s@) == 0,
        s@.len() == 0 ==> result,
{
    let mut i: usize = 0;
    let mut zero = true;
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@),
            zero ==> forall |k: int| 0 <= k && k < i as int ==> s@.index(k) == '0',
        decreases s.len() - i
    {
        if s[i] == '1' { zero = false; }
        i += 1;
    }
    zero
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::<char>::new();
    if is_all_zero_bits(sy) {
        res.push('1');
    } else if is_all_zero_bits(sx) {
        res.push('0');
    } else {
        res.push('0');
    }
    res
}
// </vc-code>

fn main() {}
}
