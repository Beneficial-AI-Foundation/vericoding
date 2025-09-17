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
/* helper modified by LLM (iteration 2): Removed unused helper (not needed as to_vec() is a builtin) */
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Used `usize` for indexing and `len()` for array sizes in `Mul_NormalizeBitString` */
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
            current_prod == 0 ==> (Str2Int(result_vec@) == prod),
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
    let mut i: usize = if result_vec.len() == 0 { 0 } else { result_vec.len() - 1 };
    while i < result_vec.len() // loop until i underflows
        invariant
            reversed_result_vec.len() + i + 1 == result_vec.len() || (result_vec.len() == 0 && reversed_result_vec.len() == 0),
            i <= result_vec.len(), 
            forall |j: int| 0 <= j && (j as usize) < reversed_result_vec.len() ==> (reversed_result_vec@[j] == result_vec@[result_vec.len() - 1 - (j as usize)]),
        decreases i
    {
        reversed_result_vec.push(result_vec@[i]);
        i = i - 1;
    }

    reversed_result_vec
}
// </vc-code>

fn main() {}
}
