// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
  s.len() > 0 && (s.len() > 1 ==> s[0] != '0') &&
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn decimal_to_binary_helper(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    decimal_to_binary_helper(n / 2).add(decimal_to_binary_helper(n % 2))
  }
}

spec fn binary_to_decimal(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() <= 0 {
    0
  } else if s.len() == 1 {
    if s[0] == '0' { 0 } else { 1 }
  } else {
    binary_to_decimal(s.take((s.len() - 1) as int)) * 2 + 
    binary_to_decimal(s.skip((s.len() - 1) as int))
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `forall` syntax. */
proof fn lemma_decimal_to_binary_pow2(k: nat)
    ensures (binary_to_decimal(decimal_to_binary_helper(k)) == k)
    decreases k
{
    if k == 0 {
        assert(decimal_to_binary_helper(0) == seq!['0']);
        assert(binary_to_decimal(seq!['0']) == 0);
    } else if k == 1 {
        assert(decimal_to_binary_helper(1) == seq!['1']);
        assert(binary_to_decimal(seq!['1']) == 1);
    } else {
        lemma_decimal_to_binary_pow2(k / 2);
        lemma_decimal_to_binary_pow2(k % 2);
        let s_div2 = decimal_to_binary_helper(k / 2);
        let s_mod2 = decimal_to_binary_helper(k % 2);
        assert(binary_to_decimal(s_div2) == k / 2);
        assert(binary_to_decimal(s_mod2) == k % 2);
        assert(s_div2.add(s_mod2) == decimal_to_binary_helper(k));

        assert(binary_to_decimal(s_div2.add(s_mod2)) == binary_to_decimal(s_div2) * 2 + binary_to_decimal(s_mod2));
        assert(binary_to_decimal(s_div2.add(s_mod2)) == (k/2)*2 + (k%2));
        assert((k/2)*2 + (k%2) == k);
    }
}

/* helper modified by LLM (iteration 5): Corrected `forall` syntax. */
proof fn lemma_is_binary_string_of_decimal_to_binary_helper(n: nat)
    ensures is_binary_string(decimal_to_binary_helper(n))
    decreases n
{
    if n == 0 {
        assert(decimal_to_binary_helper(0) == seq!['0']);
        assert(is_binary_string(seq!['0']));
    } else if n == 1 {
        assert(decimal_to_binary_helper(1) == seq!['1']);
        assert(is_binary_string(seq!['1']));
    } else {
        lemma_is_binary_string_of_decimal_to_binary_helper(n / 2);
        lemma_is_binary_string_of_decimal_to_binary_helper(n % 2);
        let s_div2 = decimal_to_binary_helper(n / 2);
        let s_mod2 = decimal_to_binary_helper(n % 2);

        assert(s_div2.len() >= 1);
        assert(s_mod2.len() == 1);
        assert(s_mod2[0] == '0' || s_mod2[0] == '1');
        let s_concat = s_div2.add(s_mod2);
        assert(s_concat.len() == s_div2.len() + s_mod2.len());
        assert(s_concat.len() >= 2);

        if n / 2 > 0 {
            assert(s_div2[0] != '0');
        }

        proof {
            forall |i: int| (0 <= i && i < s_concat.len()) implies (s_concat[i] == '0' || s_concat[i] == '1')
            {
                if i < s_div2.len() {
                    assert(s_div2[i] == '0' || s_div2[i] == '1');
                } else {
                    let j = i - s_div2.len();
                    assert(j == 0);
                    assert(s_mod2[j] == '0' || s_mod2[j] == '1');
                }
            }
        }

        assert(is_binary_string(s_concat));
    }
}
// </vc-helpers>

// <vc-spec>
fn decimal_to_binary(n: u8) -> (s: Vec<char>)
  ensures
    is_binary_string(s@),
    binary_to_decimal(s@) == n as nat,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `forall` syntax and added proof for `lemma_is_binary_string_of_decimal_to_binary_helper`. */
{
    let mut n_u64 = n as u64;
    let mut binary_vec: Vec<char> = Vec::new();

    if n_u64 == 0 {
        binary_vec.push('0');
    } else {
        while n_u64 > 0
            invariant
                n_u64 >= 0,
                binary_to_decimal(binary_vec@.add(decimal_to_binary_helper(n_u64 as nat))) == n as nat,
                forall|i: int| 0 <= i < binary_vec@.len() ==> (binary_vec@[i] == '0' || binary_vec@[i] == '1'),
            decreases n_u64
        {
            let remainder = n_u64 % 2;
            if remainder == 0 {
                binary_vec.insert(0, '0');
                proof {
                    let current_binary_seq = binary_vec@.take(binary_vec@.len() - 1);
                    let original_n_as_nat = n as nat;
                    let new_n_u64 = n_u64 / 2;
                    lemma_decimal_to_binary_pow2(new_n_u64 as nat);
                }
            } else {
                binary_vec.insert(0, '1');
                 proof {
                    let current_binary_seq = binary_vec@.take(binary_vec@.len() - 1);
                    let original_n_as_nat = n as nat;
                    let new_n_u64 = n_u64 / 2;
                    lemma_decimal_to_binary_pow2(new_n_u64 as nat);
                }
            }
            n_u64 /= 2;
        }
    }

    proof {
        if n > 0 {
            assert(binary_vec@.len() > 0);
            assert(binary_vec@[0] != '0');
        }
        lemma_decimal_to_binary_pow2(n as nat);
        lemma_is_binary_string_of_decimal_to_binary_helper(n as nat);

        assert(binary_to_decimal(binary_vec@) == n as nat);
        if n == 0 {
            assert(binary_vec@ == seq!['0']);
        }
        else {
             proof {
                forall |i: int| (0 <= i && i < binary_vec@.len()) implies (binary_vec@[i] == '0' || binary_vec@[i] == '1') 
                {
                    let mut temp_n = n as u64;
                    let mut current_binary_seq = Seq::<char>::empty();
                    if temp_n == 0 {
                        current_binary_seq = seq!['0'];
                    } else {
                        while temp_n > 0 {
                            let remainder_val = temp_n % 2;
                            if remainder_val == 0 {
                                current_binary_seq = seq!['0'].add(current_binary_seq);
                            } else {
                                current_binary_seq = seq!['1'].add(current_binary_seq);
                            }
                            temp_n /= 2;
                        }
                    }
                    assert(current_binary_seq == binary_vec@);

                    if (0 <= i && i < binary_vec@.len()) {
                        assert(binary_vec@[i] == '0' || binary_vec@[i] == '1');
                    }
                }
            }
        }
    }

    binary_vec
}
// </vc-code>


}

fn main() {}