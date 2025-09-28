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
/* helper modified by LLM (iteration 5): Fixed reverse_vec by correcting type conversions and loop logic */

proof fn lemma_no_leading_zero(n: nat)
    requires
        n > 1,
    ensures
        decimal_to_binary_helper(n)[0] == '1',
decreases n
{
    if n == 2 {
    } else if n > 2 {
        lemma_no_leading_zero(n / 2);
    }
}

proof fn lemma_binary_conversion_correct(n: nat)
    ensures
        binary_to_decimal(decimal_to_binary_helper(n)) == n,
    decreases n
{
    if n == 0 || n == 1 {
        return;
    }
    lemma_binary_conversion_correct(n / 2);
    lemma_binary_conversion_correct(n % 2);
}

fn reverse_vec(chars: &mut Vec<char>) 
    ensures
        chars@.len() == old(chars)@.len(),
        forall|i: int| 0 <= i < chars@.len() ==> chars@[i] == old(chars)@[(chars@.len() - 1 - i) as int],
{
    let mut i: usize = 0;
    let len = chars.len();
    let mut j: usize = if len > 0 { len - 1 } else { 0 };
    while i < j
        invariant
            0 <= i <= j + 1,
            j < chars@.len(),
            chars@.len() == old(chars)@.len(),
            forall|k: int| 0 <= k < chars@.len() ==> 
                (k < i || k > j) ==> chars@[k] == old(chars)@[(chars@.len() - 1 - k) as int],
                (k >= i && k <= j) ==> chars@[k] == old(chars)@[k],
        decreases j - i
    {
        let tmp = chars[i];
        chars[i] = chars[j];
        chars[j] = tmp;
        i = i + 1;
        if j > 0 { 
            j = (j as int - 1) as usize; 
        }
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
{
    /* code modified by LLM (iteration 5): Fixed while loop and verification */
    let mut num = n;
    let mut digits = Vec::new();
    
    if num == 0 {
        digits.push('0');
        return digits;
    }
    
    while num > 0
        invariant
            num as int >= 0,
            digits@.len() >= 0,
            forall|i: int| 0 <= i < digits@.len() ==> digits@[i] == '0' || digits@[i] == '1',
        decreases num
    {
        digits.push(if num % 2 == 0 { '0' } else { '1' });
        num = num / 2;
    }
    
    reverse_vec(&mut digits);
    
    proof {
        if n > 1 {
            lemma_no_leading_zero(n as nat);
        }
        lemma_binary_conversion_correct(n as nat);
    }
    
    digits
}
// </vc-code>


}

fn main() {}