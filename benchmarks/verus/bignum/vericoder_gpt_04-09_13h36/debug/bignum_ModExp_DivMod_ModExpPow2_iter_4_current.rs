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
proof fn lemma_subrange_concat_last(s: Seq<char>, c: char)
    ensures
        (s + seq![c]).subrange(0, (s + seq![c]).len() as int - 1) == s,
        (s + seq![c]).index((s + seq![c]).len() as int - 1) == c
{
    let t = s + seq![c];
    assert(t.len() == s.len() + 1);
    let last = t.len() as int - 1;
    assert(last == s.len() as int);
    // subrange 0..s.len() of s + [c] equals s
    assert(t.subrange(0, s.len() as int) == s);
    // Therefore subrange(0, last) equals s
    assert(t.subrange(0, last) == s);
    // The last element is c
    assert(t.index(last) == c);
}

proof fn lemma_Str2Int_snoc(s: Seq<char>, c: char)
    ensures
        Str2Int(s + seq![c]) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
    let t = s + seq![c];
    assert(t.len() == s.len() + 1);
    let last = t.len() as int - 1;
    lemma_subrange_concat_last(s, c);
    assert(t.subrange
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
proof fn lemma_subrange_concat_last(s: Seq<char>, c: char)
    ensures
        (s + seq![c]).subrange(0, (s + seq![c]).len() as int - 1) == s,
        (s + seq![c]).index((s + seq![c]).len() as int - 1) == c
{
    let t = s + seq![c];
    assert(t.len() == s.len() + 1);
    let last = t.len() as int - 1;
    assert(last == s.len() as int);
    // subrange 0..s.len() of s + [c] equals s
    assert(t.subrange(0, s.len() as int) == s);
    // Therefore subrange(0, last) equals s
    assert(t.subrange(0, last) == s);
    // The last element is c
    assert(t.index(last) == c);
}

proof fn lemma_Str2Int_snoc(s: Seq<char>, c: char)
    ensures
        Str2Int(s + seq![c]) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
    let t = s + seq![c];
    assert(t.len() == s.len() + 1);
    let last = t.len() as int - 1;
    lemma_subrange_concat_last(s, c);
    assert(t.subrange
// </vc-code>

fn main() {}
}