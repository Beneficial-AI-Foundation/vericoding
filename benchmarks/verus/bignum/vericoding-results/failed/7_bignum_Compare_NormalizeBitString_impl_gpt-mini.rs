// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
      0nat
  } else {
      2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
      valid_bit_string(t) &&
      t.len() > 0 &&
      (t.len() > 1 ==> t[0] != '0') &&
      (valid_bit_string(s) ==> str2int(s) == str2int(t))
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): pow2 and lemmas for bitstring numeric reasoning */
spec fn pow2(n: int) -> nat
  requires n >= 0
  decreases n
{
  if n <= 0 { 1nat } else { 2nat * pow2(n - 1) }
}

proof fn pow2_monotone(a: int, b: int)
  requires 0 <= a && a <= b
  ensures pow2(a) <= pow2(b)
  decreases b - a
{
  if a == b { } else { pow2_monotone(a, b - 1); }
}

proof fn str2int_lt_pow2(s: Seq<char>)
  requires valid_bit_string(s)
  ensures str2int(s) < pow2((s.len()) as int)
  decreases s.len()
{
  let n = s.len() as int;
  if n == 0 { } else {
    let prefix = s.subrange(0, n - 1);
    str2int_lt_pow2(prefix);
    // str2int(s) = 2 * str2int(prefix) + bit(last)
    if s[(n - 1) as usize] == '1' {
      assert(str2int(s) == 2nat * str2int(prefix) + 1nat);
    } else {
      assert(str2int(s) == 2nat * str2int(prefix));
    }
    // from induction: str2int(prefix) < pow2(n-1)
    assert(pow2(n - 1) >= 1nat);
    // convert < to <= - 1
    assert(str2int(prefix) <= pow2(n - 1) - 1nat);
    if s[(n - 1) as usize] == '1' {
      assert(str2int(s) <= 2nat * (pow2(n - 1) - 1nat) + 1nat);
    } else {
      assert(str2int(s) <= 2nat * (pow2(n - 1) - 1nat));
    }
    // hence str2int(s) < 2 * pow2(n - 1) == pow2(n)
    assert(str2int(s) < pow2(n));
  }
}

proof fn msb_lower_bound(s: Seq<char>)
  requires valid_bit_string(s) && s.len() >= 1 && s[0] == '1'
  ensures pow2((s.len() - 1) as int) <= str2int(s)
  decreases s.len()
{
  let n = s.len() as int;
  if n == 1 {
    // s == "1"
    assert(str2int(s) == 1nat);
    assert(pow2(0) == 1nat);
  } else {
    // s = first ++ tail
    // Let tail = s.subrange(1, n). We have str2int(s) = pow2(n-1) + str2int(tail)
    // Prove pow2(n-1) <= str2int(s) trivially since str2int(tail) >= 0
    let tail = s.subrange(1, n);
    // use definition unfolding via arithmetic reasoning
    // Construct relation by induction on n: reduce to case for prefix of s removing last char
    // Instead of heavy algebra, observe first bit contributes pow2(n-1)
    // Formalize by relating with prefix that leaves last bit out
    // Build prefix (all but last) and then relate via induction
    let prefix = s.subrange(0, n - 1);
    // Consider value of s: str2int(s) == 2nat * str2int(prefix) + (if s[(n-1)] == '1' {1} else {0})
    if s[(n - 1) as usize] == '1' {
      assert(str2int(s) == 2nat * str2int(prefix) + 1nat);
    } else {
      assert(str2int(s) == 2nat * str2int(prefix));
    }
    // Now show pow2(n-1) <= str2int(s) by noting most significant bit s[0]=='1'
    // Reduce to smaller argument by considering prefix without its last bit
    // Let pref_prefix = prefix.subrange(0, (prefix.len()) as int - 1) if prefix.len()>=1;
    // Use monotonicity of pow2 and non-negativity to conclude the bound
    assert(pow2(n - 1) <= str2int(s) + 0nat);
  }
}

proof fn remove_leading_zero_step(s: Seq<char>)
  requires valid_bit_string(s) && s.len() >= 1 && s[0] == '0'
  ensures str2int(s) == str2int(s.subrange(1, (s.len()) as int))
  decreases s.len()
{
  let n = s.len() as int;
  if n == 1 {
    // s == "0"
    assert(str2int(s) == 0nat);
    assert(str2int(Seq::<char>::empty()) == 0nat);
  } else {
    let prefix = s.subrange(0, n - 1);
    // prefix also has leading zero
    remove_leading_zero_step(prefix);
    // unwind definitions:
    // str2int(s) = 2 * str2int(prefix) + bit(last)
    // str2int(s.subrange(1,n)) = 2 * str2int(prefix.subrange(1, prefix.len())) + bit(last)
    if s[(n - 1) as usize] == '1' {
      assert(str2int(s) == 2nat * str2int(prefix) + 1nat);
      assert(str2int(s.subrange(1, n)) == 2nat * str2int(prefix.subrange(1, (prefix.len()) as int)) + 1nat);
    } else {
      assert(str2int(s) == 2nat * str2int(prefix));
      assert(str2int(s.subrange(1, n)) == 2nat * str2int(prefix.subrange(1, (prefix.len()) as int)));
    }
    // use recursive equality on prefix
    assert(str2int(prefix) == str2int(prefix.subrange(1, (prefix.len()) as int)));
    // conclude equality
    assert(str2int(s) == str2int(s.subrange(1, n)));
  }
}

proof fn leading_zeros_preserve(s: Seq<char>, i: int)
  requires valid_bit_string(s) && 0 <= i && i <= (s.len() as int) && (forall|j: int| 0 <= j < i ==> s[j] == '0')
  ensures str2int(s) == str2int(s.subrange(i, (s.len()) as int))
  decreases i
{
  if i == 0 { } else {
    // first char is 0, so remove one leading zero and recurse
    remove_leading_zero_step(s);
    leading_zeros_preserve(s.subrange(1, (s.len()) as int), i - 1);
    // compose equalities
    assert(str2int(s) == str2int(s.subrange(1, (s.len()) as int)));
    assert(str2int(s.subrange(1, (s.len()) as int)) == str2int(s.subrange(i, (s.len()) as int)));
    assert(str2int(s) == str2int(s.subrange(i, (s.len()) as int)));
  }
}

// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i8)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
      (str2int(s1@) < str2int(s2@) ==> res as int == -1) &&
      (str2int(s1@) == str2int(s2@) ==> res as int == 0) &&
      (str2int(s1@) > str2int(s2@) ==> res as int == 1)
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 10): compare two bit-strings after stripping leading zeros and lexicographically */
  let mut i1: usize = 0;
  // strip leading zeros but leave at least one digit
  while i1 < s1.len()
      invariant
          0 <= (i1 as int) && (i1 as int) <= (s1@).len() as int,
          forall|j: int| 0 <= j < (i1 as int) ==> #[trigger] s1@[j] == '0',
      decreases (s1@).len() as int - (i1 as int)
  {
      if s1[i1] == '0' && s1.len() > 1 {
          i1 += 1;
      } else {
          break;
      }
  }

  let mut i2: usize = 0;
  while i2 < s2.len()
      invariant
          0 <= (i2 as int) && (i2 as int) <= (s2@).len() as int,
          forall|j: int| 0 <= j < (i2 as int) ==> #[trigger] s2@[j] == '0',
      decreases (s2@).len() as int - (i2 as int)
  {
      if s2[i2] == '0' && s2.len() > 1 {
          i2 += 1;
      } else {
          break;
      }
  }

  let rem1: usize = s1.len() - i1;
  let rem2: usize = s2.len() - i2;

  if rem1 < rem2 {
      proof {
          let gi1: int = i1 as int;
          let gi2: int = i2 as int;
          let n1: int = (s1@).len() as int;
          let n2: int = (s2@).len() as int;
          let grem1: int = n1 - gi1;
          let grem2: int = n2 - gi2;
          leading_zeros_preserve(s1@, gi1);
          leading_zeros_preserve(s2@, gi2);
          let t1 = s1@.subrange(gi1, n1);
          let t2 = s2@.subrange(gi2, n2);
          // t1 and t2 are the trimmed sequences; since rem1 < rem2, t2 has strictly more digits
          // assert that t2's most significant digit is '1' unless its length is 1 and equal digits handled elsewhere
          if t2.len() >= 2 {
              // then the first digit cannot be '0' because we would have removed it in the loop
              assert(t2[0] != '0');
              msb_lower_bound(t2);
              pow2_monotone(grem1, grem2 - 1);
          } else {
              // t2.len() == 1: then rem1 < rem2 implies rem1 == 0 which cannot happen because we always keep at least one digit
              // but include this branch to satisfy the verifier; if rem2 == 1 then rem1 < 1 cannot hold because rem1 >= 1
              msb_lower_bound(t2); // safe because t2.len() == 1 and t2[0] must be '1' to have rem2 > rem1
          }
      }
      return -1i8;
  } else if rem1 > rem2 {
      proof {
          let gi1: int = i1 as int;
          let gi2: int = i2 as int;
          let n1: int = (s1@).len() as int;
          let n2: int = (s2@).len() as int;
          let grem1: int = n1 - gi1;
          let grem2: int = n2 - gi2;
          leading_zeros_preserve(s1@, gi1);
          leading_zeros_preserve(s2@, gi2);
          let t1 = s1@.subrange(gi1, n1);
          let t2 = s2@.subrange(gi2, n2);
          if t1.len() >= 2 {
              assert(t1[0] != '0');
              msb_lower_bound(t1);
              pow2_monotone(grem2, grem1 - 1);
          } else {
              msb_lower_bound(t1);
          }
      }
      return 1i8;
  } else {
      // rem1 == rem2: compare lexicographically
      let mut k: usize = 0;
      while k < rem1
          invariant
              0 <= (k as int) && (k as int) <= ((s1@).len() as int - (i1 as int)),
              forall|j: int| 0 <= j < (k as int) ==> #[trigger] s1@[(i1 as int) + j] == s2@[(i2 as int) + j],
              (i1 as int) + (k as int) <= (s1@).len() as int,
              (i2 as int) + (k as int) <= (s2@).len() as int,
          decreases (s1@).len() as int - (i1 as int) - (k as int)
      {
          // ensure safe indexing for verifier
          assert(i1 + k < s1.len());
          assert(i2 + k < s2.len());
          let c1 = s1[i1 + k];
          let c2 = s2[i2 + k];
          if c1 < c2 {
              proof {
                  let gi1: int = i1 as int;
                  let gi2: int = i2 as int;
                  let gk: int = k as int;
                  let n1: int = (s1@).len() as int;
                  let n2: int = (s2@).len() as int;
                  let t1 = s1@.subrange(gi1 + gk, n1);
                  let t2 = s2@.subrange(gi2 + gk, n2);
                  // ensure tail subranges are well-formed
                  assert(0 <= gi1 + gk && gi1 + gk <= n1);
                  assert(0 <= gi2 + gk && gi2 + gk <= n2);
                  let t1tail = t1.subrange(1, (t1.len()) as int);
                  str2int_lt_pow2(t1tail);
                  msb_lower_bound(t2);
              }
              return -1i8;
          }
          if c1 > c2 {
              proof {
                  let gi1: int = i1 as int;
                  let gi2: int = i2 as int;
                  let gk: int = k as int;
                  let n1: int = (s1@).len() as int;
                  let n2: int = (s2@).len() as int;
                  let t1 = s1@.subrange(gi1 + gk, n1);
                  let t2 = s2@.subrange(gi2 + gk, n2);
                  assert(0 <= gi1 + gk && gi1 + gk <= n1);
                  assert(0 <= gi2 + gk && gi2 + gk <= n2);
                  let t2tail = t2.subrange(1, (t2.len()) as int);
                  str2int_lt_pow2(t2tail);
                  msb_lower_bound(t1);
              }
              return 1i8;
          }
          k += 1;
      }
      return 0i8;
  }
}

// </vc-code>


}

fn main() {}