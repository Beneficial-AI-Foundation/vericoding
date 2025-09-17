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
/* helper modified by LLM (iteration 6): removed redundant types in tuple return */
spec fn add_bitstrings_helper(s1_bit_val: nat, s2_bit_val: nat, carry_in: nat) -> (c_out: nat, s_out: nat)
    requires
        s1_bit_val == 0 || s1_bit_val == 1,
        s2_bit_val == 0 || s2_bit_val == 1,
        carry_in == 0 || carry_in == 1,
    ensures
        (c_out == 0 || c_out == 1),
        (s_out == 0 || s_out == 1),
        s1_bit_val + s2_bit_val + carry_in == c_out * 2 + s_out,
{
    let sum = s1_bit_val + s2_bit_val + carry_in;
    let s_out_val = sum % 2;
    let c_out_val = sum / 2;
    (c_out_val, s_out_val)
}
spec fn add(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    requires ValidBitString(s1), ValidBitString(s2)
    ensures ValidBitString(add(s1, s2)),
            Str2Int(add(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
    add_recursive(s1, s2, 0)
}
spec fn add_recursive(s1: Seq<char>, s2: Seq<char>, carry_in: nat) -> Seq<char>
    requires ValidBitString(s1), ValidBitString(s2),
             carry_in == 0 || carry_in == 1,
    ensures ValidBitString(add_recursive(s1, s2, carry_in)),
            Str2Int(add_recursive(s1, s2, carry_in)) == Str2Int(s1) + Str2Int(s2) + carry_in
    decreases s1.len() + s2.len()
{
    {
        if s1.len() == 0 && s2.len() == 0 {
            if carry_in == 1 { seq!['1'] } else { seq![] }
        } else {
            let s1_bit_val: nat = if s1.len() > 0 && s1.last() == Option::Some('1') { 1 } else { 0 };
            let s2_bit_val: nat = if s2.len() > 0 && s2.last() == Option::Some('1') { 1 } else { 0 };

            let (carry_out, sum_bit) = add_bitstrings_helper(s1_bit_val, s2_bit_val, carry_in);

            let new_s1 = if s1.len() > 0 { s1.drop_last() } else { s1 };
            let new_s2 = if s2.len() > 0 { s2.drop_last() } else { s2 };

            let res_suffix = if sum_bit == 1 { '1' } else { '0' };
            add_recursive(new_s1, new_s2, carry_out).push(res_suffix)
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
/* code modified by LLM (iteration 6): no functional changes, compilation error was in vc-helpers */
{
    let s1_seq = s1@;
    let s2_seq = s2@;

    if s1_seq.len() == 0 || s2_seq.len() == 0 {
        return Vec::<char>::new();
    }

    let mut results: Vec<Seq<char>> = Vec::new();

    let mut i: usize = s2_seq.len() - 1;
    while i < s2_seq.len()
        invariant
            0 <= i + 1,
            (i as int) < (s2_seq.len() as int),
            results.len() == (s2_seq.len() - (i + 1)) as int,
            forall |k: int| 0 <= k && k < results.len() ==> ValidBitString(results.index(k))
        decreases i
    {
        let mut current_product_seq: Seq<char>;
        let current_bit = s2_seq.index(i);

        if current_bit == '1' {
            current_product_seq = s1_seq;
        } else {
            current_product_seq = seq![]; // All zeros implicitly
        }

        let num_trailing_zeros: usize = s2_seq.len() - 1 - i;
        let mut j: usize = 0;
        while j < num_trailing_zeros
            invariant
                0 <= j <= num_trailing_zeros,
                current_product_seq.len() >= s1_seq.len() + (j as int),
                ValidBitString(current_product_seq)
            decreases num_trailing_zeros - j
        {
            current_product_seq = current_product_seq.push('0');
            j = j + 1;
        }

        results.push(current_product_seq);
        if i == 0 {
            // End loop condition when i reaches 0
            break;
        }
        i = i - 1;
    }

    let mut final_sum_seq: Seq<char> = seq![];
    if results.len() > 0 {
        final_sum_seq = results.index(0);
        let mut k: usize = 1;
        while k < results.len()
            invariant
                1 <= k && k <= results.len(),
                ValidBitString(final_sum_seq),
                forall |idx: int| 0 <= idx && idx < k ==> ValidBitString(results.index(idx))
            decreases results.len() - k
        {
            final_sum_seq = add(final_sum_seq, results.index(k));
            k = k + 1;
        }
    }

    Vec::from_slice(&final_sum_seq)
}
// </vc-code>

fn main() {}
}
