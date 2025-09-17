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
spec fn add(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    requires ValidBitString(s1), ValidBitString(s2)
    ensures ValidBitString(add(s1, s2)),
            Str2Int(add(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
    if s1.len() == 0 && s2.len() == 0 {
        seq![]
    } else if s1.len() == 0 {
        s2
    } else if s2.len() == 0 {
        s1
    } else {
        let c1 = if s1.ends_with(seq!['1']) { 1 } else { 0 };
        let c2 = if s2.ends_with(seq!['1']) { 1 } else { 0 };
        let sum = c1 + c2;

        let carry = if sum >= 2 { 1 } else { 0 };
        let digit = if sum % 2 == 1 { '1' } else { '0' };

        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);

        let carried_s2_prefix = if carry == 1 {
            // Add 1 to s2_prefix
            let mut rev_s2_prefix = s2_prefix.reversed();
            let mut i = 0;
            let mut new_rev_s2_prefix = seq![];
            let mut c = 1;
            while i < rev_s2_prefix.len()
                invariant
                    0 <= i <= rev_s2_prefix.len(),
                    new_rev_s2_prefix.len() == i,
                    c == 0 || c == 1,
                    forall |j|
                        0 <= j < i ==> new_rev_s2_prefix.index(j) == '0' || new_rev_s2_prefix.index(j) == '1'
            {
                let digit_val = if rev_s2_prefix.index(i) == '1' { 1 } else { 0 };
                let sum_val = digit_val + c;
                if sum_val == 2 {
                    new_rev_s2_prefix = new_rev_s2_prefix.push('0');
                    c = 1;
                } else if sum_val == 1 {
                    new_rev_s2_prefix = new_rev_s2_prefix.push('1');
                    c = 0;
                } else {
                    new_rev_s2_prefix = new_rev_s2_prefix.push('0');
                    c = 0;
                }
                i = i + 1;
            }
            if c == 1 {
                new_rev_s2_prefix = new_rev_s2_prefix.push('1');
            }
            new_rev_s2_prefix.reversed()
        } else {
            s2_prefix
        };
        add(s1_prefix, carried_s2_prefix).push(digit)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let s1_seq = s1@;
    let s2_seq = s2@;

    if s1_seq.len() == 0 || s2_seq.len() == 0 {
        return Vec::<char>::new();
    }

    let mut results: Vec<Seq<char>> = Vec::new();

    let mut i = (s2_seq.len() as int - 1) as int;
    while i >= 0
        invariant
            0 <= i + 1 <= s2_seq.len(),
            results.len() == s2_seq.len() as int - (i + 1),
            forall |k: int| 0 <= k < results.len() ==> ValidBitString(results.index(k))
        decreases i
    {
        let mut current_product_seq = seq![];
        let current_bit = s2_seq.index(i);

        if current_bit == '1' {
            current_product_seq = s1_seq;
        } else {
            current_product_seq = seq![]; // All zeros implicitly
        }

        let num_trailing_zeros = (s2_seq.len() as int - 1) - i;
        let mut j = 0;
        while j < num_trailing_zeros
            invariant
                0 <= j <= num_trailing_zeros,
                current_product_seq.len() >= s1_seq.len(),
                forall |k: int| 0 <= k < current_product_seq.len() ==> current_product_seq.index(k) == '0'
                                                      || current_product_seq.index(k) == '1'
            decreases j
        {
            current_product_seq = current_product_seq.push('0');
            j = j + 1;
        }

        results.push(current_product_seq);
        i = i - 1;
    }

    let mut final_sum_seq: Seq<char> = seq![];
    if results.len() > 0 {
        final_sum_seq = results.index(0);
        let mut k = 1;
        while k < results.len()
            invariant
                1 <= k <= results.len(),
                ValidBitString(final_sum_seq)
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
