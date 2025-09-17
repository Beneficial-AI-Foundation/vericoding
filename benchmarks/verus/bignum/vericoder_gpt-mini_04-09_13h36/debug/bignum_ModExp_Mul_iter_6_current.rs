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
spec fn CharBit(c: char) -> nat {
    if c == '1' { 1 } else { 0 }
}

proof fn lemma_str2int_all_zero(s: Seq<char>)
    requires s.len() >= 0
    ensures (forall |i: int| 0 <= i && i < s.len() ==> s.index(i) == '0') ==> Str2Int(s) == 0
{
    if s.len() == 0 {
    } else {
        lemma_str2int_all_zero(s.subrange(0, s.len() as int - 1));
        if s.index(s.len() as int - 1) == '0' {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 0);
            assert((forall |i: int| 0 <= i && i < s.subrange(0, s.len() as int - 1).len() ==> s.subrange(0, s.len() as int - 1).index(i) == '0'));
            assert(Str2Int(s.subrange(0, s.len() as int - 1)) == 0);
            assert(Str2Int(s) == 0);
        } else {
        }
    }
}

proof fn lemma_str2int_concat(s: Seq<char>, b: char)
    ensures Str2Int(s + seq![b]) == 2 * Str2Int(s) + CharBit(b)
{
    if s.len() == 0 {
        assert(Str2Int(seq![b]) == (if b == '1' { 1 } else { 0 }));
        assert(2 * Str2Int(seq![]) + CharBit(b) == CharBit(b));
    } else {
        let t = s + seq![b];
        // t.len() = s.len() + 1, and t.subrange(0, t.len()-1) = s
        assert(t.subrange(0, t.len() as int - 1) == s);
        // unfold definition of Str2Int on t
        assert(Str2Int(t) == 2 * Str2Int(t.subrange(0, t.len() as int - 1)) + (if t.index(t.len() as int - 1) == '1' { 1 } else { 0 }));
        assert(t.index(t.len() as int -
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
spec fn CharBit(c: char) -> nat {
    if c == '1' { 1 } else { 0 }
}

proof fn lemma_str2int_all_zero(s: Seq<char>)
    requires s.len() >= 0
    ensures (forall |i: int| 0 <= i && i < s.len() ==> s.index(i) == '0') ==> Str2Int(s) == 0
{
    if s.len() == 0 {
    } else {
        lemma_str2int_all_zero(s.subrange(0, s.len() as int - 1));
        if s.index(s.len() as int - 1) == '0' {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 0);
            assert((forall |i: int| 0 <= i && i < s.subrange(0, s.len() as int - 1).len() ==> s.subrange(0, s.len() as int - 1).index(i) == '0'));
            assert(Str2Int(s.subrange(0, s.len() as int - 1)) == 0);
            assert(Str2Int(s) == 0);
        } else {
        }
    }
}

proof fn lemma_str2int_concat(s: Seq<char>, b: char)
    ensures Str2Int(s + seq![b]) == 2 * Str2Int(s) + CharBit(b)
{
    if s.len() == 0 {
        assert(Str2Int(seq![b]) == (if b == '1' { 1 } else { 0 }));
        assert(2 * Str2Int(seq![]) + CharBit(b) == CharBit(b));
    } else {
        let t = s + seq![b];
        // t.len() = s.len() + 1, and t.subrange(0, t.len()-1) = s
        assert(t.subrange(0, t.len() as int - 1) == s);
        // unfold definition of Str2Int on t
        assert(Str2Int(t) == 2 * Str2Int(t.subrange(0, t.len() as int - 1)) + (if t.index(t.len() as int - 1) == '1' { 1 } else { 0 }));
        assert(t.index(t.len() as int -
// </vc-code>

fn main() {}
}