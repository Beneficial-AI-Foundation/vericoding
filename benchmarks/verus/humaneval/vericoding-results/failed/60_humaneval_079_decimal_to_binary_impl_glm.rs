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
fn decimal_to_binary_exec(n: u8) -> (s: Vec<char>)
    decreases n
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else {
        let rest = decimal_to_binary_exec(n / 2);
        let last = if n % 2 == 0 { '0' } else { '1' };
        let mut result = rest;
        result.push(last);
        result
    }
}

proof fn lemma_decimal_to_binary_exec(n: u8)
    decreases n
    ensures
        is_binary_string(decimal_to_binary_exec(n)@),
        binary_to_decimal(decimal_to_binary_exec(n)@) == n as nat
{
    if n == 0 {
        assert(is_binary_string(seq!['0']));
        assert(binary_to_decimal(seq!['0']) == 0);
    } else if n == 1 {
        assert(is_binary_string(seq!['1']));
        assert(binary_to_decimal(seq!['1']) == 1);
    } else {
        let rest = decimal_to_binary_exec(n / 2);
        let last_digit = if n % 2 == 0 { '0' } else { '1' };
        let s = rest@ + seq![last_digit];

        lemma_decimal_to_binary_exec(n / 2);

        if n % 2 == 0 {
            lemma_decimal_to_binary_exec(0);
            assert(binary_to_decimal(seq![last_digit]) == 0);
        } else {
            lemma_decimal_to_binary_exec(1);
            assert(binary_to_decimal(seq![last_digit]) == 1);
        }

        if rest@.len() == 1 {
            assert(rest@[0] == '1');
        } else {
            assert(rest@[0] != '0');
        }
        assert(is_binary_string(s));

        assert(binary_to_decimal(s) == binary_to_decimal(rest@) * 2 + binary_to_decimal(seq![last_digit]));
        let quotient = n / 2;
        let remainder = n % 2;
        assert(quotient * 2 + remainder == n);
        assert((quotient as nat) * 2 + (remainder as nat) == n as nat);
        assert(binary_to_decimal(s) == n as nat);
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
    let result = decimal_to_binary_exec(n);
    proof {
        lemma_decimal_to_binary_exec(n);
    }
    result
}
// </vc-code>


}

fn main() {}