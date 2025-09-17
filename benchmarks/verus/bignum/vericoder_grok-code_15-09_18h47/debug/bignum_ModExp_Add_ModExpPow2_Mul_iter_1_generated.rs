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
spec fn nat2bin(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else if n % 2 == 0 {
        nat2bin(n / 2).push('0')
    } else {
        nat2bin(n / 2).push('1')
    }
}

proof fn lemma_nat2bin_valid(n: nat)
    ensures ValidBitString(nat2bin(n))
    decreases n
{
    // Proof by induction
}

proof fn lemma_nat2bin_str2int(n: nat, s: Seq<char>)
    requires s == nat2bin(n)
    ensures Str2Int(s) == n
    decreases n
{
    // Proof by induction
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    spec {
        let a_num = Str2Int(a@);
        let b_num = Str2Int(b@);
        let res_num = a_num * b_num;
        let res_seq = nat2bin(res_num);
    }
    let mut res = Vec::<char>::new();
    for i in 0..res_seq.len() {
        proof {
        }
        res.push(res_seq[i]);
    }
    proof {
        lemma_nat2bin_valid(res_num);
        lemma_nat2bin_str2int(res_num, res_seq);
    }
    res
}
// </vc-code>

fn main() {}
}

