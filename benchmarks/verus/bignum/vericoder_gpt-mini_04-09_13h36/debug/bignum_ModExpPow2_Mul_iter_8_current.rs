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

exec fn seq_to_usize(s: &[char]) -> (ret: usize)
  requires ValidBitString(s@)
  ensures Str2Int(s@) == ret as nat
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = seq_to_usize(&s[0..s.len()-1]);
        let bit = if s[s.len()-1] == '1' { 1usize } else { 0usize };
        let r = prefix * 2 + bit;
        proof {
            // By the recursive ensures of seq_to_usize on the prefix
            assert(Str2Int(s@.subrange(0, s.len() as int - 1)) == prefix as nat);
            // By definition of Str2Int on the whole sequence
            assert(Str2Int(s@) == 2 * Str2Int(s@.subrange(0, s.len() as int - 1)) + (if s@.index(s.len() as int - 1) == '1' { 1 } else { 0 }));
            assert(Str2Int(s@) == 2 * (prefix as nat) + (bit as nat));
            assert(Str2Int(s@) == r as nat);
        }
        r
    }
}

exec fn usize_to_vec(n: usize) -> (v: Vec<char>)
  ensures v@ == Nat_to_seq(n as nat)
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut v = usize_to_vec(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        proof {
            assert(v@ == Nat_to_seq((n / 2) as nat) + seq![bit]);
            assert(v@ == Nat_to_seq(n as nat));
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
    let n1 = seq_to_usize(s1);
    let n2 = seq_to_usize(s2);
    let prod = n1 * n2;
    let res = usize_to_vec(prod);
    proof {
        // Relate the computed usize values to the specification Str2Int
        assert(Str2Int(s1@) == n1 as nat);
        assert(Str2Int(s2@) == n2 as nat);
        // Use lemma for the produced vector
        lemma_nat_to_seq_valid(prod as nat);
        assert(ValidBitString(res@));
        lemma_nat_to_seq_correct(prod as nat);
        assert(Str2Int(res@) == prod as nat);
        assert(Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@));
    }
    res
}
// </vc-code>

fn main() {}
}