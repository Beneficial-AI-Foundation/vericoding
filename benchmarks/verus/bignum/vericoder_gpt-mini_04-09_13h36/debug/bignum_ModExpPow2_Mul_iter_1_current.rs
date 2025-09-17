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
use vstd::pervasive::seq::*;
use vstd::pervasive::seq;

proof fn lemma_exp_int_mul(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases a, b
{
    if b == 0 {
        assert(Exp_int(x, a + 0) == Exp_int(x, a) * 1);
    } else {
        lemma_exp_int_mul(x, a, b - 1);
        assert(Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1)));
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a) * (x * Exp_int(x, b - 1)));
    }
}

proof fn lemma_str2int_concat(a: Seq<char>, b: Seq<char>)
  requires ValidBitString(a)
  requires ValidBitString(b)
  ensures Str2Int(a + b) == Str2Int(a) * Exp_int(2, b.len()) + Str2Int(b)
  decreases a.len()
{
    if a.len() == 0 {
        assert(a + b == b);
        assert(Str2Int(a + b) == Str2Int(b));
        assert(Str2Int(a) == 0);
        assert(Exp_int(2, b.len()) >= 1);
    } else {
        // write a as a0 ++ [last]
        let n = a.len();
        let last = a.index((n as int) - 1);
        let a_prefix = a.subrange(0, (n as int) - 1);
        // a + b = a_prefix ++ [last] ++ b
        // By definition Str2Int(a_plus_b) = 2 * Str2Int((a + b).subrange(0, len-1)) + lastbit
        assert(Str2Int(a + b) == 2 * Str2Int((a + b).subrange(0, (a + b).len() as int - 1)) + (if (a + b).index((a + b).len() as int - 1) == '1' { 1 } else { 0 }));
        // The last element of a + b is the last element of b if b non-empty, else it's last of a.
        // But easier: use associativity: (a_prefix + seq![last]) + b == a_prefix + (seq![last] + b)
        // Consider s = a_prefix + (seq![last] + b)
        // Apply inductive hypothesis on a_prefix
        lemma_str2int_concat(a_prefix, seq![last] + b);
        // Now Str2Int(a_prefix + (seq![last] + b)) == Str2Int(a_prefix) * Exp_int(2, (seq![last] + b).len()) + Str2Int(seq![last] + b)
        // Also compute Str2Int(seq![last] + b) = Str2Int(seq![last]) * Exp_int(2, b.len()) + Str2Int(b)
        // Str2Int(seq![last]) is (if last == '1' {1} else {0})
        // Combine equalities to get desired result.
        // Formal steps:
        let left = Str2Int(a + b);
        let mid = Str2Int(a_prefix) * Exp_int(2, (seq![last] + b).len()) + Str2Int(seq![last] + b);
        assert(left == mid); // from above lemma application
        let s_last = Str2Int(seq![last] + b);
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
// <vc-helpers>
use vstd::pervasive::seq::*;
use vstd::pervasive::seq;

proof fn lemma_exp_int_mul(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases a, b
{
    if b == 0 {
        assert(Exp_int(x, a + 0) == Exp_int(x, a) * 1);
    } else {
        lemma_exp_int_mul(x, a, b - 1);
        assert(Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1)));
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a) * (x * Exp_int(x, b - 1)));
    }
}

proof fn lemma_str2int_concat(a: Seq<char>, b: Seq<char>)
  requires ValidBitString(a)
  requires ValidBitString(b)
  ensures Str2Int(a + b) == Str2Int(a) * Exp_int(2, b.len()) + Str2Int(b)
  decreases a.len()
{
    if a.len() == 0 {
        assert(a + b == b);
        assert(Str2Int(a + b) == Str2Int(b));
        assert(Str2Int(a) == 0);
        assert(Exp_int(2, b.len()) >= 1);
    } else {
        // write a as a0 ++ [last]
        let n = a.len();
        let last = a.index((n as int) - 1);
        let a_prefix = a.subrange(0, (n as int) - 1);
        // a + b = a_prefix ++ [last] ++ b
        // By definition Str2Int(a_plus_b) = 2 * Str2Int((a + b).subrange(0, len-1)) + lastbit
        assert(Str2Int(a + b) == 2 * Str2Int((a + b).subrange(0, (a + b).len() as int - 1)) + (if (a + b).index((a + b).len() as int - 1) == '1' { 1 } else { 0 }));
        // The last element of a + b is the last element of b if b non-empty, else it's last of a.
        // But easier: use associativity: (a_prefix + seq![last]) + b == a_prefix + (seq![last] + b)
        // Consider s = a_prefix + (seq![last] + b)
        // Apply inductive hypothesis on a_prefix
        lemma_str2int_concat(a_prefix, seq![last] + b);
        // Now Str2Int(a_prefix + (seq![last] + b)) == Str2Int(a_prefix) * Exp_int(2, (seq![last] + b).len()) + Str2Int(seq![last] + b)
        // Also compute Str2Int(seq![last] + b) = Str2Int(seq![last]) * Exp_int(2, b.len()) + Str2Int(b)
        // Str2Int(seq![last]) is (if last == '1' {1} else {0})
        // Combine equalities to get desired result.
        // Formal steps:
        let left = Str2Int(a + b);
        let mid = Str2Int(a_prefix) * Exp_int(2, (seq![last] + b).len()) + Str2Int(seq![last] + b);
        assert(left == mid); // from above lemma application
        let s_last = Str2Int(seq![last] + b);
// </vc-code>

fn main() {}
}