use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
// Helper lemmas for proving properties about Str2Int
proof fn lemma_str2int_zero(n: nat)
    ensures Str2Int(Seq::new(n, |_| '0')) == 0
    decreases n
{
    if n > 0 {
        lemma_str2int_zero((n - 1) as nat);
    }
}

proof fn lemma_str2int_shift(s: Seq<char>, n: nat)
    requires ValidBitString(s)
    ensures 
        ValidBitString(Seq::new(n, |_| '0') + s),
        Str2Int(Seq::new(n, |_| '0') + s) == Str2Int(s) * pow2(n)
    decreases n
{
    if n == 0 {
        assert(Seq::new(0, |_| '0') + s =~= s);
    } else {
        let zeros_n = Seq::new(n, |_| '0');
        let zeros_n_minus_1 = Seq::new((n - 1) as nat, |_| '0');
        lemma_str2int_shift(s, (n - 1) as nat);
        assert(zeros_n =~= Seq::new(1, |_| '0') + zeros_n_minus_1);
        assert(zeros_n + s =~= Seq::new(1, |_| '0') +
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
// Helper lemmas for proving properties about Str2Int
proof fn lemma_str2int_zero(n: nat)
    ensures Str2Int(Seq::new(n, |_| '0')) == 0
    decreases n
{
    if n > 0 {
        lemma_str2int_zero((n - 1) as nat);
    }
}

proof fn lemma_str2int_shift(s: Seq<char>, n: nat)
    requires ValidBitString(s)
    ensures 
        ValidBitString(Seq::new(n, |_| '0') + s),
        Str2Int(Seq::new(n, |_| '0') + s) == Str2Int(s) * pow2(n)
    decreases n
{
    if n == 0 {
        assert(Seq::new(0, |_| '0') + s =~= s);
    } else {
        let zeros_n = Seq::new(n, |_| '0');
        let zeros_n_minus_1 = Seq::new((n - 1) as nat, |_| '0');
        lemma_str2int_shift(s, (n - 1) as nat);
        assert(zeros_n =~= Seq::new(1, |_| '0') + zeros_n_minus_1);
        assert(zeros_n + s =~= Seq::new(1, |_| '0') +
// </vc-code>

fn main() {}
}