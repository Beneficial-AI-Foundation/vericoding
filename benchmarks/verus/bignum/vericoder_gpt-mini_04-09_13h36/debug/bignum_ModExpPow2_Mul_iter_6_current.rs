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
use vstd::seq::seq;

spec fn Nat_to_seq(n: nat) -> Seq<char>
  decreases n
{
    if n == 0 {
        seq![]
    } else {
        let prefix = Nat_to_seq((n / 2) as nat);
        prefix + seq![ if n % 2 == 1 { '1' } else { '0' } ]
    }
}

proof fn lemma_nat_to_seq_correct(n: nat)
  ensures Str2Int(Nat_to_seq(n)) == n
  decreases n
{
    if n == 0 {
        assert(Str2Int(Nat_to_seq(0)) == 0);
    } else {
        lemma_nat_to_seq_correct((n / 2) as nat);
        let prefix = Nat_to_seq((n / 2) as nat);
        let bit: nat = (if n % 2 == 1 { 1 } else { 0 }) as nat;
        assert(Str2Int(prefix + seq![ if n % 2 == 1 { '1' } else { '0' } ]) == 2 * Str2Int(prefix) + bit);
        assert(Str2Int(prefix) == (n / 2) as nat);
        assert(2 * ((n / 2) as nat) + ((n % 2) as nat) == n);
        assert(Str2Int(Nat_to_seq(n)) == n);
    }
}

proof fn lemma_nat_to_seq_valid(n: nat)
  ensures ValidBitString(Nat_to_seq(n))
  decreases n
{
    if n == 0 {
        assert(ValidBitString(Nat_to_seq(0)));
    } else {
        lemma_nat_to_seq_valid((n / 2) as nat);
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
        let mut v = nat_to_vec((n / 2) as nat);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        proof {
            assert(v@ == Nat_to_seq((n / 2) as nat) + seq![bit]);
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