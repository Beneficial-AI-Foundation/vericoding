// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn digits_sum_pos(n: int) -> int
  decreases n
{
  if n >= 0 {
    if n < 10 { n } else { digits_sum_pos(n / 10) + n % 10 }
  } else {
    0
  }
}

spec fn digits_sum(n: int) -> int {
  if n < 0 { digits_sum_pos(-n) } else { digits_sum_pos(n) }
}
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(s: Seq<i8>) -> bool
    decreases 0int
{
    forall |i:int, j:int| 0 <= i < j < s.len() ==> digits_sum(s[i] as int) <= digits_sum(s[j] as int)
}

/* helper modified by LLM (iteration 4): Fixed compilation errors by avoiding 'int' type in executable code, using 'i32' for absolute value calculation instead. */

fn digit_sum(n: i8) -> (res: i32)
    ensures
        res == digits_sum(n as int),
{
    let abs_val: i32 = if n < 0 { -(n as i32) } else { n as i32 };
    let mut sum = 0i32;
    let mut num = abs_val;
    while num > 0
        invariant
            sum as int + digits_sum_pos(num as int) == digits_sum_pos(abs_val as int),
            num >= 0,
        decreases num
    {
        sum += num % 10;
        num /= 10;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn order_by_points(s: Vec<i8>) -> (sorted: Vec<i8>)
  ensures 
      forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> digits_sum(sorted@[i] as int) <= digits_sum(sorted@[j] as int),
      sorted@.len() == s@.len(),
      s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): No changes to implementation logic; relies on fixed helper function to resolve compilation errors. */
{
    let mut sorted = Vec::with_capacity(s.len());
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            sorted@.len() == i,
            s@.multiset() == sorted@.multiset() + s@.subrange(i as int, s@.len() as int),
            is_sorted(sorted@),
        decreases s@.len() - i
    {
        let elem = s[i];
        let elem_key = digit_sum(elem);
        let mut pos = 0;
        while pos < sorted.len() && digit_sum(sorted[pos]) <= elem_key
            invariant
                pos <= sorted.len(),
                forall |k:int| 0 <= k < pos ==> digits_sum(sorted@[k] as int) <= elem_key as int,
                forall |k:int| pos <= k < sorted.len() ==> digits_sum(sorted@[k] as int) > elem_key as int,
            decreases sorted.len() - pos
        {
            pos += 1;
        }
        sorted.insert(pos, elem);
        i += 1;
    }
    sorted
}
// </vc-code>


}

fn main() {}