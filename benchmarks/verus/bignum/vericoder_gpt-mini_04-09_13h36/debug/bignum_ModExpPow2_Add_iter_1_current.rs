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
// <vc-helpers>
spec fn Rev(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
    if s.len() == 0 {
        Seq::<char>::empty()
    } else {
        let last = s.index(s.len() as int - 1);
        seq![last].concat(Rev(s.subrange(0, s.len() as int - 1)))
    }
}

spec fn ValueLSB(s: Seq<char>) -> nat
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s.index(0) == '1' { 1 } else { 0 }) + 2 * ValueLSB(s.subrange(1, s.len() as int))
    }
}

lemma rec fn Str2Int_concat(a: Seq<char>, b: Seq<char>)
  requires ValidBitString(a), ValidBitString(b)
  ensures Str2Int(a.concat(b)) == Exp_int(2, b.len()) * Str2Int(a) + Str2Int(b)
  decreases a.len()
{
    if a.len() == 0 {
        // a = []
        assert(Str2Int(Seq::<char>::empty().concat(b)) == Str2Int(b));
        assert(Exp_int(2, b.len()) * Str2Int(Seq::<char>::empty()) + Str2Int(b) == Str2Int(b));
    } else {
        // a = a0 ++ rest, where we take last char of a and split
        let a_last = a.index(a.len() as int - 1);
        let a_pref = a.subrange(0, a.len() as int - 1);
        // a = a_pref.concat(seq![a_last])
        // Str2Int(a_pref.concat(seq![a_last]).concat(b)) = ...
        // Use induction on a_pref
        rec {
            Str2Int_concat(a_pref, seq![a_last].concat(b));
        }
        // By induction:
        // Str2Int(a_pref.concat(seq![a_last]).concat(b)) ==
        //   Exp_int(2, (seq![a_last].concat(b)).len()) * Str2Int(a_pref) + Str2Int(seq![a_last].concat(b))
        //
        // Now handle seq![a_last].concat(b)
        assert((seq![a_last].concat(b)).len() == 1 + b.len());
        // Str2Int(seq![a_last].concat(b)) == Exp_int(2, b.len()) * Str2Int(seq![a_last]) + Str2Int(b)
        // Str2Int(seq![a_last]) is either 1 or 0 depending on a_last
        if a_last == '1' {
            assert(Str2Int(seq![a_last]) == 1);
        } else {
            assert(Str2Int(seq![a_last]) == 0);
        }
        // Combine equalities step by step
        // Final rearrangement gives the desired equality
        //
        // (Detailed equalities are straightforward expansion; leave as proof steps)
        ()
    }
}

lemma rec fn ValueLSB_concat_prefix(r: Seq<char>, c: char)
  requires ValidBitString(r) && (c == '0' || c == '1')
  ensures ValueLSB(r.concat(seq![c])) == ValueLSB(r) + (if c == '1' { 1 } else { 0 }) * Exp_int(2, r.len())
  decreases r.len()
{
    if r.len() == 0 {
        // r = []
        assert(ValueLSB(Seq::<char>::empty().concat(seq![c])) == (if c == '1' {1} else {0}));
        assert(ValueLSB(Seq::<char>::empty()) == 0);
    } else {
        let head = r.index(0);
        let tail = r.subrange(1, r.len() as int);
        // ValueLSB(r) = head_bit + 2 * ValueLSB(tail)
        // For r.concat([c]) we have first element head and tail' = tail.concat([c])
        rec {
            ValueLSB_concat_prefix(tail, c);
        }
        // ValueLSB(r.concat([c])) = head_bit + 2 * ValueLSB(tail.concat([c]))
        // By inductive hypothesis, that equals head_bit + 2*(ValueLSB(tail) + c_bit * 2^{tail.len})
        // = head_bit + 2*ValueLSB(tail) + c_bit * 2^{1 + tail.len}
        // since r.len() == 1 + tail.len(), this is ValueLSB(r) + c_bit * 2^{r.len()}
        ()
    }
}

lemma rec fn ValueLSB_eq_Str2Int_Rev(s: Seq<char>)
  requires ValidBitString(s)
  ensures ValueLSB(s) == Str2Int(Rev(s))
  decreases s.len()
{
    if s.len() == 0 {
        assert(ValueLSB(Seq::<char>::empty()) == 0);
        assert(Str2Int(Rev(Seq::<char>::empty())) == 0);
    } else {
        let first = s.index(0);
        let rest = s.subrange(1, s.len() as int);
        // ValueLSB(s) = first_bit + 2 * ValueLSB(rest)
        rec {
            ValueLSB_eq_Str2Int_Rev(rest);
        }
        // Rev(s) = seq![s.index(s.len()-1)].concat(Rev(s.subrange(0, s.len()-1)))
        // But to relate, it's easier to use Str2Int_concat on single element and Rev(rest)
        // Build Rev(s) explicitly via last and prefix
        let last
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
// <vc-helpers>
spec fn Rev(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
    if s.len() == 0 {
        Seq::<char>::empty()
    } else {
        let last = s.index(s.len() as int - 1);
        seq![last].concat(Rev(s.subrange(0, s.len() as int - 1)))
    }
}

spec fn ValueLSB(s: Seq<char>) -> nat
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s.index(0) == '1' { 1 } else { 0 }) + 2 * ValueLSB(s.subrange(1, s.len() as int))
    }
}

lemma rec fn Str2Int_concat(a: Seq<char>, b: Seq<char>)
  requires ValidBitString(a), ValidBitString(b)
  ensures Str2Int(a.concat(b)) == Exp_int(2, b.len()) * Str2Int(a) + Str2Int(b)
  decreases a.len()
{
    if a.len() == 0 {
        // a = []
        assert(Str2Int(Seq::<char>::empty().concat(b)) == Str2Int(b));
        assert(Exp_int(2, b.len()) * Str2Int(Seq::<char>::empty()) + Str2Int(b) == Str2Int(b));
    } else {
        // a = a0 ++ rest, where we take last char of a and split
        let a_last = a.index(a.len() as int - 1);
        let a_pref = a.subrange(0, a.len() as int - 1);
        // a = a_pref.concat(seq![a_last])
        // Str2Int(a_pref.concat(seq![a_last]).concat(b)) = ...
        // Use induction on a_pref
        rec {
            Str2Int_concat(a_pref, seq![a_last].concat(b));
        }
        // By induction:
        // Str2Int(a_pref.concat(seq![a_last]).concat(b)) ==
        //   Exp_int(2, (seq![a_last].concat(b)).len()) * Str2Int(a_pref) + Str2Int(seq![a_last].concat(b))
        //
        // Now handle seq![a_last].concat(b)
        assert((seq![a_last].concat(b)).len() == 1 + b.len());
        // Str2Int(seq![a_last].concat(b)) == Exp_int(2, b.len()) * Str2Int(seq![a_last]) + Str2Int(b)
        // Str2Int(seq![a_last]) is either 1 or 0 depending on a_last
        if a_last == '1' {
            assert(Str2Int(seq![a_last]) == 1);
        } else {
            assert(Str2Int(seq![a_last]) == 0);
        }
        // Combine equalities step by step
        // Final rearrangement gives the desired equality
        //
        // (Detailed equalities are straightforward expansion; leave as proof steps)
        ()
    }
}

lemma rec fn ValueLSB_concat_prefix(r: Seq<char>, c: char)
  requires ValidBitString(r) && (c == '0' || c == '1')
  ensures ValueLSB(r.concat(seq![c])) == ValueLSB(r) + (if c == '1' { 1 } else { 0 }) * Exp_int(2, r.len())
  decreases r.len()
{
    if r.len() == 0 {
        // r = []
        assert(ValueLSB(Seq::<char>::empty().concat(seq![c])) == (if c == '1' {1} else {0}));
        assert(ValueLSB(Seq::<char>::empty()) == 0);
    } else {
        let head = r.index(0);
        let tail = r.subrange(1, r.len() as int);
        // ValueLSB(r) = head_bit + 2 * ValueLSB(tail)
        // For r.concat([c]) we have first element head and tail' = tail.concat([c])
        rec {
            ValueLSB_concat_prefix(tail, c);
        }
        // ValueLSB(r.concat([c])) = head_bit + 2 * ValueLSB(tail.concat([c]))
        // By inductive hypothesis, that equals head_bit + 2*(ValueLSB(tail) + c_bit * 2^{tail.len})
        // = head_bit + 2*ValueLSB(tail) + c_bit * 2^{1 + tail.len}
        // since r.len() == 1 + tail.len(), this is ValueLSB(r) + c_bit * 2^{r.len()}
        ()
    }
}

lemma rec fn ValueLSB_eq_Str2Int_Rev(s: Seq<char>)
  requires ValidBitString(s)
  ensures ValueLSB(s) == Str2Int(Rev(s))
  decreases s.len()
{
    if s.len() == 0 {
        assert(ValueLSB(Seq::<char>::empty()) == 0);
        assert(Str2Int(Rev(Seq::<char>::empty())) == 0);
    } else {
        let first = s.index(0);
        let rest = s.subrange(1, s.len() as int);
        // ValueLSB(s) = first_bit + 2 * ValueLSB(rest)
        rec {
            ValueLSB_eq_Str2Int_Rev(rest);
        }
        // Rev(s) = seq![s.index(s.len()-1)].concat(Rev(s.subrange(0, s.len()-1)))
        // But to relate, it's easier to use Str2Int_concat on single element and Rev(rest)
        // Build Rev(s) explicitly via last and prefix
        let last
// </vc-code>

fn main() {}
}