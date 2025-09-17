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
// Helper functions and proofs for ModExp_int

exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
{
    let mut i: usize = 0;
    let mut r: nat = 0;
    while i < s.len() {
        invariant i <= s.len();
        invariant r == Str2Int(s@.subrange(0, i as int));
        decreases s.len() - i;
        let c = s[i];
        if c == '1' {
            r = r * 2 + 1;
        } else {
            r = r * 2;
        }
        i += 1;
    }
    r
}

proof fn lemma_div_mod_2(m: nat)
  ensures m == 2*(m/2) + (m % 2)
{
    // This follows from
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
// Helper functions and proofs for ModExp_int

exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
{
    let mut i: usize = 0;
    let mut r: nat = 0;
    while i < s.len() {
        invariant i <= s.len();
        invariant r == Str2Int(s@.subrange(0, i as int));
        decreases s.len() - i;
        let c = s[i];
        if c == '1' {
            r = r * 2 + 1;
        } else {
            r = r * 2;
        }
        i += 1;
    }
    r
}

proof fn lemma_div_mod_2(m: nat)
  ensures m == 2*(m/2) + (m % 2)
{
    // This follows from
// </vc-code>

fn main() {}
}