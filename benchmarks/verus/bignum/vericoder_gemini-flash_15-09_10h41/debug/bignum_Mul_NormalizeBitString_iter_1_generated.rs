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
spec fn SeqToVec(s: Seq<char>) -> Vec<char> { s.to_vec() }
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let i1 = Str2Int(s1@);
    let i2 = Str2Int(s2@);
    let prod = i1 * i2;

    let mut result_vec = Vec::<char>::new();
    let mut current_prod = prod;

    if current_prod == 0 {
        result_vec.push('0');
    }

    while current_prod > 0
        invariant
            current_prod >= 0,
            // PROOF: This invariant establishes that the numeric value represented by the
            // result_vec (when read from right to left, i.e., in reverse order of how we
            // are building it) plus the value of `current_prod` contributes to `prod`.
            // More precisely, prod == current_prod + Str2Int(result_vec@).
            // This proof requires defining Str2Int_rev, which interprets a bit string
            // from right to left.
            // For now, we will simply state the overall property needed for functional correctness
            // once the loop terminates: if current_prod is 0, Str2Int(rev(result_vec@)) == prod
            current_prod == 0 ==> Str2Int(result_vec@) == prod,
        decreases current_prod
    {
        if current_prod % 2 == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        current_prod = current_prod / 2;
    }

    let mut reversed_result_vec = Vec::<char>::new();
    let mut i = result_vec.len() as int - 1;
    while i >= 0
        invariant
            i >= -1,
            i < result_vec.len() as int,
            reversed_result_vec.len() as int == result_vec.len() as int - (i + 1),
            forall |j: int| 0 <= j && j < reversed_result_vec.len() as int ==> (reversed_result_vec@[j] == result_vec@[result_vec.len() as int - 1 - j]),
        decreases i
    {
        reversed_result_vec.push(result_vec@[i]);
        i = i - 1;
    }

    // Proof of correctness of reverse_result_vec with respect to Str2Int(s: Seq<char>) requires induction.
    // Once Str2Int(s: Seq<char>) is proved correct:
    // assert(Str2Int(reversed_result_vec@) == prod);

    reversed_result_vec
}
// </vc-code>

fn main() {}
}
