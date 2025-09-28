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
proof fn lemma_binary_to_decimal_single_digit(c: char)
    requires
        c == '0' || c == '1',
    ensures
        binary_to_decimal(seq![c]) == if c == '0' { 0 } else { 1 },
{
}

proof fn lemma_decimal_to_binary_helper_is_binary(n: nat)
    ensures
        is_binary_string(decimal_to_binary_helper(n)),
    decreases n
{
    if n == 0 {
        assert(decimal_to_binary_helper(0) == seq!['0']);
        assert(is_binary_string(seq!['0']));
    } else if n == 1 {
        assert(decimal_to_binary_helper(1) == seq!['1']);
        assert(is_binary_string(seq!['1']));
    } else {
        lemma_decimal_to_binary_helper_is_binary(n / 2);
        lemma_decimal_to_binary_helper_is_binary(n % 2);
        assert(n % 2 == 0 || n % 2 == 1);
        if n % 2 == 0 {
            assert(decimal_to_binary_helper(n % 2) == seq!['0']);
        } else {
            assert(decimal_to_binary_helper(n % 2) == seq!['1']);
        }
        let left = decimal_to_binary_helper(n / 2);
        let right = decimal_to_binary_helper(n % 2);
        assert(right.len() == 1);
        assert(right[0] == '0' || right[0] == '1');
        let combined = left.add(right);
        assert(combined.len() == left.len() + 1);
        assert forall|i: int| 0 <= i < combined.len() implies (combined[i] == '0' || combined[i] == '1') by {
            if i < left.len() {
                assert(combined[i] == left[i]);
            } else {
                assert(i == left.len());
                assert(combined[i] == right[0]);
            }
        }
        if n / 2 > 1 {
            assert(left[0] != '0');
            assert(combined[0] == left[0]);
            assert(combined[0] != '0');
        }
        assert(is_binary_string(combined));
    }
}

proof fn lemma_binary_to_decimal_inverse(n: nat)
    ensures
        binary_to_decimal(decimal_to_binary_helper(n)) == n,
    decreases n
{
    if n == 0 {
        assert(decimal_to_binary_helper(0) == seq!['0']);
        assert(binary_to_decimal(seq!['0']) == 0);
    } else if n == 1 {
        assert(decimal_to_binary_helper(1) == seq!['1']);
        assert(binary_to_decimal(seq!['1']) == 1);
    } else {
        lemma_binary_to_decimal_inverse(n / 2);
        lemma_binary_to_decimal_inverse(n % 2);
        let left = decimal_to_binary_helper(n / 2);
        let right = decimal_to_binary_helper(n % 2);
        assert(n % 2 == 0 || n % 2 == 1);
        assert(right.len() == 1);
        let combined = left.add(right);
        assert(combined.take((combined.len() - 1) as int) == left);
        assert(combined.skip((combined.len() - 1) as int) == right);
        assert(binary_to_decimal(combined) == binary_to_decimal(left) * 2 + binary_to_decimal(right));
        assert(binary_to_decimal(left) == n / 2);
        assert(binary_to_decimal(right) == n % 2);
        assert(n / 2 * 2 + n % 2 == n);
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
    let n_nat = n as nat;
    proof {
        lemma_decimal_to_binary_helper_is_binary(n_nat);
        lemma_binary_to_decimal_inverse(n_nat);
    }
    
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        assert(result@ == seq!['0']);
        assert(result@ == decimal_to_binary_helper(0));
        return result;
    } else if n == 1 {
        let mut result = Vec::new();
        result.push('1');
        assert(result@ == seq!['1']);
        assert(result@ == decimal_to_binary_helper(1));
        return result;
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        let mut digits: Vec<char> = Vec::new();
        
        while temp > 0
            invariant
                0 <= temp <= n,
                digits@.len() >= 0,
                forall|i: int| 0 <= i < digits@.len() ==> (digits@[i] == '0' || digits@[i] == '1'),
        {
            if temp % 2 == 0 {
                digits.push('0');
            } else {
                digits.push('1');
            }
            temp = temp / 2;
        }
        
        let mut i: usize = digits.len();
        while i > 0
            invariant
                0 <= i <= digits.len(),
                result@.len() == digits.len() - i,
                forall|j: int| 0 <= j < result@.len() ==> result@[j] == digits@[digits@.len() - 1 - j],
                forall|j: int| 0 <= j < result@.len() ==> (result@[j] == '0' || result@[j] == '1'),
        {
            i = i - 1;
            result.push(digits[i]);
        }
        
        assert(result@.len() > 0);
        assert(result@ == decimal_to_binary_helper(n_nat));
        return result;
    }
}
// </vc-code>


}

fn main() {}