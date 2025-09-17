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
fn seq_to_nat(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        2 * seq_to_nat(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
    }
}

proof fn seq_to_nat_eq_Str2Int(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        seq_to_nat(s) == Str2Int(s),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        seq_to_nat_eq_Str2Int(s.subrange(0, s.len() as int - 1));
    }
}

fn nat_to_vec_rec(n: nat) -> Vec<char>
    decreases n
{
    let mut v = Vec::<char>::new();
    if n == 0 {
        v.push('0');
        v
    } else if n == 1 {
        v.push('1');
        v
    } else {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        let mut prefix = nat_to_vec_rec(n / 2);
        prefix.push(bit);
        prefix
    }
}

proof fn nat_to_vec_correct(n: nat)
    ensures
        ValidBitString(nat_to_vec_rec(n)@),
        Str2Int(nat_to_vec_rec(n)@) == n,
    decreases n
{
    if n == 0 {
    } else if n == 1 {
    } else {
        nat_to_vec_correct(n / 2);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = seq_to_nat(s1@);
    let n2 = seq_to_nat(s2@);
    let diff: nat = n1 - n2;
    let res = nat_to_vec_rec(diff);
    proof {
        seq_to_nat_eq_Str2Int(s1@);
        seq_to_nat_eq_Str2Int(s2@);
        nat_to_vec_correct(diff);
    }
    res
}
// </vc-code>

fn main() {}
}


