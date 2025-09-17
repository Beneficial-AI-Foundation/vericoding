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
/* helper modified by LLM (iteration 4): seq_to_nat and nat_to_vec_rec with safe reverse indexing invariants */
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
        while m > 0
            decreases m
        {
            let bit = if m % 2 == 1 { '1' } else { '0' };
            rev.push(bit);
            m = m / 2;
        }
        let mut out = Vec::<char>::new();
        let mut i: usize = rev.len();
        while i > 0
            invariant
                i <= rev.len(),
            decreases i
        {
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
    /* code modified by LLM (iteration 4): bitwise subtraction from LSB with borrow, then reverse result */
    let mut i: usize = s1.len();
    let mut j: usize = s2.len();
    let mut rev = Vec::<char>::new();
    let mut borrow: u8 = 0;
    while i > 0 || j > 0
        invariant
            borrow <= 1,
            rev.len() <= s1.len() + s2.len(),
        decreases (i + j)
    {
        let b1 = if i > 0 && s1[i - 1] == '1' { 1 } else { 0 };
        let b2 = if j > 0 && s2[j - 1] == '1' { 1 } else { 0 };
        let sub = (b1 as i8) - (b2 as i8) - (borrow as i8);
        if sub < 0 {
            rev.push('1');
            borrow = 1;
        } else if sub == 0 {
            rev.push('0');
            borrow = 0;
        } else {
            rev.push('1');
            borrow = 0;
        }
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }
    // Reverse rev (LSB-first) into out (MSB-first)
    let mut out = Vec::<char>::new();
    let mut k: usize = rev.len();
    while k > 0
        invariant
            k <= rev.len(),
        decreases k
    {
        k -= 1;
        out.push(rev[k]);
    }
    proof {
        seq_to_nat_eq_Str2Int(s1@);
        seq_to_nat_eq_Str2Int(s2@);
    }
    out
}
// </vc-code>

fn main() {}
}


