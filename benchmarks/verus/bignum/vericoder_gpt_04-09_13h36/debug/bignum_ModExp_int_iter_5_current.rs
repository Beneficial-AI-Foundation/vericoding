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
spec fn Bin(k: nat) -> Seq<char>
    decreases k
{
    if k == 0 {
        Seq::<char>::empty()
    } else {
        let tail = Bin(k / 2);
        tail.push(if k % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_Bin
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
spec fn Bin(k: nat) -> Seq<char>
    decreases k
{
    if k == 0 {
        Seq::<char>::empty()
    } else {
        let tail = Bin(k / 2);
        tail.push(if k % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_Bin
// </vc-code>

fn main() {}
}