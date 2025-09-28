// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_digits(x: int) -> Seq<int>
  recommends x >= 0
{
  if x == 0 { seq![0] }
  else { int_to_digits_helper(x) }
}

spec fn int_to_digits_helper(x: int) -> Seq<int>
  recommends x > 0
  decreases x
{
  if x < 10 { seq![x] }
  else { int_to_digits_helper(x / 10).add(seq![x % 10]) }
}

spec fn digit_sum(digits: Seq<int>) -> int
  decreases digits.len()
{
  if digits.len() == 0 { 0 }
  else { digits[0] + digit_sum(digits.subrange(1, digits.len() as int)) }
}

spec fn valid_input(x: int) -> bool
{
  x >= 1
}

spec fn valid_result(x: int, result: int) -> bool
  recommends valid_input(x)
{
  result > 0 &&
  result <= x &&
  (forall|y: int| 1 <= y <= x ==> digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(result))) &&
  (forall|y: int| 1 <= y <= x && digit_sum(int_to_digits(y)) == digit_sum(int_to_digits(result)) ==> y <= result)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that digit_sum distributes over seq.add */
spec fn lemma_digit_sum_add(s: Seq<int>, e: int)
  decreases s.len()
  ensures digit_sum(s.add(seq![e])) == digit_sum(s) + e
{
    if s.len() == 0 {
    } else {
        lemma_digit_sum_add(s.subrange(1, s.len() as int), e);
        assert(digit_sum(s) == s[0] + digit_sum(s.subrange(1, s.len() as int)));
        assert(digit_sum(s.add(seq![e])) == s[0] + digit_sum(s.subrange(1, s.len() as int).add(seq![e])));
        assert(digit_sum(s.subrange(1, s.len() as int).add(seq![e])) == digit_sum(s.subrange(1, s.len() as int)) + e);
        assert(digit_sum(s.add(seq![e])) == digit_sum(s) + e);
    }
}

/* helper modified by LLM (iteration 5): executable digit sum connecting to spec digit_sum */
fn digit_sum_exec(n: i32) -> i32
    requires n >= 0,
    ensures result == digit_sum(int_to_digits(n as int)),
    decreases n
{
    if n == 0 {
        0
    } else if n < 10 {
        n
    } else {
        let d: i32 = n % 10;
        let q: i32 = n / 10;
        let rec: i32 = digit_sum_exec(q);
        proof {
            // Relate int_to_digits(n) to int_to_digits(q).add(seq![d]) and use lemma
            assert(n >= 10);
            assert(q > 0);
            assert(int_to_digits(n as int) == int_to_digits_helper(n as int));
            assert(int_to_digits_helper(n as int) == int_to_digits_helper(q as int).add(seq![d as int]));
            assert(int_to_digits_helper(q as int) == int_to_digits(q as int));
            lemma_digit_sum_add(int_to_digits(q as int), d as int);
            assert(rec == digit_sum(int_to_digits(q as int)));
            assert(d as int + rec == digit_sum(int_to_digits(q as int).add(seq![d as int])));
            assert(d as int + rec == digit_sum(int_to_digits(n as int)));
        }
        d + rec
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
  requires valid_input(x as int)
  ensures valid_result(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate 1..=x tracking best index with largest digit sum */
    let mut best: i8 = 1;
    let mut best_sum: i32 = digit_sum_exec(1 as i32);
    let mut y: i8 = 2;
    while y <= x
        invariant
            1 <= best as int <= x as int,
            (best_sum as int) == digit_sum(int_to_digits(best as int)),
            forall|z: int| 1 <= z <= (y as int) - 1 ==> digit_sum(int_to_digits(z)) <= (best_sum as int),
            forall|z: int| 1 <= z <= (y as int) - 1 && digit_sum(int_to_digits(z)) == (best_sum as int) ==> z <= best as int,
        decreases (x as int) - (y as int) + 1
    {
        let cur_sum: i32 = digit_sum_exec(y as i32);
        if cur_sum > best_sum || (cur_sum == best_sum && (y as i32) > (best as i32)) {
            best = y;
            best_sum = cur_sum;
        }
        y = y + 1;
    }
    let result: i8 = best;
    result
}

// </vc-code>


}

fn main() {}