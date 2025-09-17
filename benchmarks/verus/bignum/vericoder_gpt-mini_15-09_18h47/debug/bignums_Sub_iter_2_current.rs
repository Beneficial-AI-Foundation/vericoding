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
/* helper modified by LLM (iteration 2): spec conversion from Seq<char> to nat, equality lemma, and executable nat->Vec conversion */
spec fn seq_to_nat(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * seq_to_nat(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
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

fn nat_to_vec_rec(n: u128) -> Vec<char>
{
    let mut v = Vec::<char>::new();
    if n == 0 {
        v.push('0');
        v
    } else {
        let mut rev = Vec::<char>::new();
        let mut m = n;
        while m > 0 {
            let bit = if m % 2 == 1 { '1' } else { '0' };
            rev.push(bit);
            m = m / 2;
        }
        let mut out = Vec::<char>::new();
        let mut i: usize = rev.len();
        while i > 0 {
            i -= 1;
            out.push(rev[i]);
        }
        out
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
    /* code modified by LLM (iteration 2): compute u128 values from input slices and build binary Vec */
    let mut n1: u128 = 0;
    let mut n2: u128 = 0;
    for i in 0..s1.len() {
        n1 = n1 * 2 + if s1[i] == '1' { 1 } else { 0 };
    }
    for i in 0..s2.len() {
        n2 = n2 * 2 + if s2[i] == '1' { 1 } else { 0 };
    }
    let diff: u128 = n1 - n2;
    let res = nat_to_vec_rec(diff);
    proof {
        seq_to_nat_eq_Str2Int(s1@);
        seq_to_nat_eq_Str2Int(s2@);
    }
    res
}

// </vc-code>

fn main() {}
}


