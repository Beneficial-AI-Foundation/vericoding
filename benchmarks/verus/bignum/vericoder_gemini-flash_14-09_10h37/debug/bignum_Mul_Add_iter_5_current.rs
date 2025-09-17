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
/* helper modified by LLM (iteration 5): Corrected the usage of `last_opt()` which returns an `Option<char>`, and simplified the final `add_bit_strings` call to manage carrying correctly. */
spec fn add_bit_strings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    recommends ValidBitString(s1), ValidBitString(s2)
{
    if s1.len() == 0 && s2.len() == 0 {
        seq![]
    } else if s1.len() == 0 {
        s2
    } else if s2.len() == 0 {
        s1
    } else {
        let last_char1 = s1.last();
        let last_char2 = s2.last();
        let sum = (if last_char1 == '1' { 1int } else { 0int }) + (if last_char2 == '1' { 1int } else { 0int });

        if sum == 0 {
            add_bit_strings(s1.drop_last(), s2.drop_last()).add(seq!['0'])
        } else if sum == 1 {
            add_bit_strings(s1.drop_last(), s2.drop_last()).add(seq!['1'])
        } else {
            // sum == 2, so carry becomes 1
            let new_s1 = s1.drop_last();
            let new_s2 = s2.drop_last();
            
            let res_without_last = add_bit_strings(add_bit_strings(new_s1, new_s2), seq!['1']); // add carry
            res_without_last.add(seq!['0'])
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `Seq::new` and `Seq::index` arguments from `usize` to `int` or `nat` as required by Verus. Also fixed `Seq<char>` indexing with `@` and ensured proper conversion between `Vec<char>` and `Seq<char>`. */
{
  let s1_vec: Vec<char> = s1.to_vec();
  let s2_vec: Vec<char> = s2.to_vec();

  let len1 = s1_vec.len();
  let len2 = s2_vec.len();

  if len1 == 0 || len2 == 0 {
    return Vec::<char>::new();
  }

  let mut products: Vec<Vec<char>> = Vec::new();

  for i in 0..len2 {
    let mut current_product: Vec<char> = Vec::new();
    // Add zeros for padding
    for _ in 0..i {
      current_product.push('0');
    }

    let digit2 = s2_vec[len2 - 1 - i];

    let mut carry = 0;
    for j in 0..len1 {
      let digit1 = s1_vec[len1 - 1 - j];
      let val1 = if digit1 == '1' { 1 } else { 0 };
      let val2 = if digit2 == '1' { 1 } else { 0 };

      let product = val1 * val2 + carry;
      current_product.push(if product % 2 == 1 { '1' } else { '0' });
      carry = product / 2;
    }
    if carry > 0 {
      current_product.push(if carry == 1 { '1' } else { '0' });
    }
    products.push(current_product.into_iter().rev().collect());
  }

  if products.is_empty() {
      return Vec::<char>::new();
  }

  let mut final_sum_vec = products[0].clone();
  
  for k in 1..products.len() {
    let s1_seq = Seq::new(final_sum_vec.len() as nat, |i: nat| final_sum_vec.is_constant() && final_sum_vec@[i as int]);
    let s2_seq = Seq::new(products[k].len() as nat, |i: nat| products[k].is_constant() && products[k]@[i as int]);

    let current_sum_seq = add_bit_strings(s1_seq, s2_seq);
    
    final_sum_vec = Vec::new();
    for l in 0..current_sum_seq.len() {
        final_sum_vec.push(current_sum_seq.index(l as int));
    }
  }

  final_sum_vec
}
// </vc-code>

fn main() {}
}
