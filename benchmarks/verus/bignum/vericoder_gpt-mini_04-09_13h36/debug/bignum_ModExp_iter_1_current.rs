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
// <vc-helpers>

use vstd::vec::Vec;

exec fn seq_to_nat(s: &[char]) -> (n: nat)
  ensures n == Str2Int(s@)
{
    // Compute Str2Int by iterating left-to-right (MSB-first)
    let mut i: nat = 0;
    let mut acc: nat = 0;
    while i < s.len()
        invariant i <= s.len()
        invariant acc == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        let bit = if s[i] == '1' { 1 } else { 0 };
        // update acc to include s[i]
        acc = 2 * acc + bit;
        // prove relation for new i
        i = i + 1;
        proof {
            // By definition of Str2Int:
            // Str2Int(s.subrange(0, i+1)) = 2 * Str2Int(s.subrange(0, i)) + bit_at_i
            // We have acc_old == Str2Int(subrange(0,i)),
            // and acc_new = 2*acc_old + bit, so invariant holds.
            assert(acc == Str2Int(s@.subrange(0, i as int)));
        }
    }
    acc
}

lemma Str2Int_prepend(c: char, s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(seq![c] + s) == Exp_int(2, s.len() as nat) * (if c == '1' { 1 } else { 0 }) + Str2Int(s)
  decreases s.len()
{
    if s.len() == 0 {
        // seq![c] has length 1, Str2Int(seq![c]) = (if c=='1' then 1 else 0)
        assert(Str2Int(seq![c]) == (if c == '1' { 1 } else { 0 }));
    } else {
        // Let last be s.index(s.len()-1)
        let last = s.index(s.len() as int - 1);
        // Consider s0 = s.subrange(0, s.len()-1)
        let s0 = s.subrange(0, s.len() as int - 1);
        // Use definition on seq![c] + s:
        // Str2Int(seq![c] + s) = 2 * Str2Int((seq![c] + s).subrange(0, len-1)) + last
        // but (seq![c] + s).subrange(0, len-1) = seq![c] + s0
        Str2Int_prepend(c, s0);
        // Now expand via definition:
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
// <vc-helpers>

use vstd::vec::Vec;

exec fn seq_to_nat(s: &[char]) -> (n: nat)
  ensures n == Str2Int(s@)
{
    // Compute Str2Int by iterating left-to-right (MSB-first)
    let mut i: nat = 0;
    let mut acc: nat = 0;
    while i < s.len()
        invariant i <= s.len()
        invariant acc == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        let bit = if s[i] == '1' { 1 } else { 0 };
        // update acc to include s[i]
        acc = 2 * acc + bit;
        // prove relation for new i
        i = i + 1;
        proof {
            // By definition of Str2Int:
            // Str2Int(s.subrange(0, i+1)) = 2 * Str2Int(s.subrange(0, i)) + bit_at_i
            // We have acc_old == Str2Int(subrange(0,i)),
            // and acc_new = 2*acc_old + bit, so invariant holds.
            assert(acc == Str2Int(s@.subrange(0, i as int)));
        }
    }
    acc
}

lemma Str2Int_prepend(c: char, s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(seq![c] + s) == Exp_int(2, s.len() as nat) * (if c == '1' { 1 } else { 0 }) + Str2Int(s)
  decreases s.len()
{
    if s.len() == 0 {
        // seq![c] has length 1, Str2Int(seq![c]) = (if c=='1' then 1 else 0)
        assert(Str2Int(seq![c]) == (if c == '1' { 1 } else { 0 }));
    } else {
        // Let last be s.index(s.len()-1)
        let last = s.index(s.len() as int - 1);
        // Consider s0 = s.subrange(0, s.len()-1)
        let s0 = s.subrange(0, s.len() as int - 1);
        // Use definition on seq![c] + s:
        // Str2Int(seq![c] + s) = 2 * Str2Int((seq![c] + s).subrange(0, len-1)) + last
        // but (seq![c] + s).subrange(0, len-1) = seq![c] + s0
        Str2Int_prepend(c, s0);
        // Now expand via definition:
// </vc-code>

fn main() {}
}