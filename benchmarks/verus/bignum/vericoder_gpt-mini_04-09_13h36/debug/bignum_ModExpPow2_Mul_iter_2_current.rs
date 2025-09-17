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
        // Exp_int definition: Exp_int(x, k+1) == x * Exp_int(x, k)
        assert(Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1)));
        assert(Exp_int(x, b) == x * Exp_int(x, b - 1));
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a) * (x * Exp_int(x, b - 1)));
        // from IH: Exp_int(x, a + (b - 1)) == Exp_int(x, a) * Exp_int(x, b - 1)
        assert(Exp_int(x, a + b) == x * (Exp_int(x, a) * Exp_int(x, b - 1)));
        assert(x * (Exp_int(x, a) * Exp_int(x, b - 1)) == Exp_int(x, a) * (x * Exp_int(x, b - 1)));
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
        let n = a.len();
        let last = a.index((n as int) - 1);
        let a_prefix = a.subrange(0, (n as int) - 1);
        // apply IH to a_prefix and seq![last] + b
        lemma_str2int_concat(a_prefix, seq![last] + b);
        // Str2Int(a_prefix + (seq![last] + b)) == Str2Int(a_prefix) * Exp_int(2, (seq![last] + b).len()) + Str2Int(seq![last] + b)
        // but a = a_prefix + seq![last], so a + b == a_prefix + (seq![last] + b)
        assert(a + b == a_prefix + (seq![last] + b));
        assert(Str2Int(a + b) == Str2Int(a_prefix) * Exp_int(2, (seq![last] + b).len()) + Str2Int(seq![last] + b));
        // compute Str2Int(seq![last] + b) by definition
        assert(Str2Int(seq![last] + b) == Str2Int(seq![last]) * Exp_int(2, b.len()) + Str2Int(b));
        // Str2Int(seq![last]) is bit value of last char
        assert(Str2Int(seq![last]) == (if last == '1' { 1 } else { 0 }));
        // (seq![last] + b).len() == b.len() + 1
        assert((seq![last] + b).len() == b.len() + 1);
        // Use lemma_exp_int_mul to expand Exp_int(2, b.len() + 1) == Exp_int(2,1) * Exp_int(2, b.len()) == 2 * Exp_int(2, b.len())
        lemma_exp_int_mul(2, 1, b.len());
        assert(Exp_int(2, (seq![last] + b).len()) == Exp_int(2, 1) * Exp_int(2, b.len()));
        assert(Exp_int(2, 1) == 2);
        assert(Exp_int(2, (seq![last] + b).len()) == 2 * Exp_int(2, b.len()));
        // combine equalities:
        // Str2Int(a + b) == Str2Int(a_prefix) * (2 * Exp_int(2, b.len())) + (Str2Int(seq![last]) * Exp_int(2, b.len()) + Str2Int(b))
        assert(Str2Int(a + b) == Str2Int(a_prefix) * (2 * Exp_int(2, b.len())) + Str2Int(seq![last]) * Exp_int(2, b.len()) + Str2Int(b));
        // regroup: = (2 * Str2Int(a_prefix) + Str2Int(seq![last])) * Exp_int(2, b.len()) + Str2Int(b)
        assert(2 * Str2Int(a_prefix) + Str2Int(seq![last]) == Str2Int(a));
        assert(Str2Int(a + b) == Str2Int(a) * Exp_int(2, b.len()) + Str2Int(b));
    }
}

spec fn Nat_to_seq(n: nat) -> Seq<char>
  decreases n
{
    if n == 0 {
        seq![]
    } else {
        let prefix = Nat_to_seq(n / 2);
        prefix + seq![ if n % 2 == 1 { '1' } else { '0' } ]
    }
}

proof fn lemma_nat_to_seq_correct(n: nat)
  ensures Str2Int(Nat_to_seq(n)) == n
  decreases n
{
    if n == 0 {
        assert(Str2Int(Nat_to_seq(0)) == Str2Int(seq![]));
        assert(Str2Int(seq![]) == 0);
    } else {
        lemma_nat_to_seq_correct(n / 2);
        let prefix = Nat_to_seq(n / 2);
        let bit = if n % 2 == 1 { 1 } else { 0 };
        // Str2Int(prefix + seq![ch]) == 2 * Str2Int(prefix) + bit
        assert(Str2Int(prefix + seq![ if n % 2 == 1 { '1' } else { '0' } ]) == 2 * Str2Int(prefix) + bit);
        // by IH Str2Int(prefix) == n / 2
        assert(Str2Int(prefix) == n / 2);
        // arithmetic: 2*(n/2) + (n % 2) == n
        assert(2 * (n / 2) + (n % 2) == n);
        assert(Str2Int(Nat_to_seq(n)) == n);
    }
}

proof fn lemma_nat_to_seq_valid(n: nat)
  ensures ValidBitString(Nat_to_seq(n))
  decreases n
{
    if n == 0 {
        assert(Nat_to_seq(0) == seq![]);
        assert(ValidBitString(seq![]));
    } else {
        lemma_nat_to_seq_valid(n / 2);
        // last char is either '0' or '1'
        let ch = if n % 2 == 1 { '1' } else { '0' };
        assert(ch == '0' || ch == '1');
        assert(ValidBitString(Nat_to_seq(n)));
    }
}

exec fn nat_to_vec(n: nat) -> (v: Vec<char>)
  ensures v@ == Nat_to_seq(n)
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut v = nat_to_vec(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        proof {
            // from recursive ensures v@ == Nat_to_seq(n/2)
            assert(v@ == Nat_to_seq(n / 2) + seq![bit]);
            assert(v@ == Nat_to_seq(n));
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let prod = n1 * n2;
    let res = nat_to_vec(prod);
    proof {
        lemma_nat_to_seq_valid(prod);
        assert(ValidBitString(res@));
        lemma_nat_to_seq_correct(prod);
        assert(Str2Int(res@) == prod);
        assert(Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@));
    }
    res
}
// </vc-code>

fn main() {}
}