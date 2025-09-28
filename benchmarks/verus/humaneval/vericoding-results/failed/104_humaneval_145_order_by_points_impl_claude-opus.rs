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
/* helper modified by LLM (iteration 4): Added executable version of digits_sum */
fn exec_digits_sum(n: i8) -> (sum: i32)
    ensures sum == digits_sum(n as int)
{
    let mut result: i32 = 0;
    let mut num: i32 = if n < 0 { -(n as i32) } else { n as i32 };
    
    while num > 0
        invariant
            num >= 0,
            result >= 0,
            digits_sum_pos(num as int) + result as int == digits_sum_pos(if n < 0 { -(n as int) } else { n as int }),
        decreases num
    {
        result = result + (num % 10);
        num = num / 10;
    }
    
    result
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
{
    /* code modified by LLM (iteration 4): Added missing decreases clause to outer loop */
    let mut sorted = s.clone();
    let n = sorted.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            sorted@.len() == s@.len(),
            s@.to_multiset() == sorted@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < i ==> digits_sum(sorted@[k] as int) <= digits_sum(sorted@[l] as int),
            forall|k: int, l: int| 0 <= k < i && i <= l < sorted@.len() ==> digits_sum(sorted@[k] as int) <= digits_sum(sorted@[l] as int),
            i <= n,
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                sorted@.len() == s@.len(),
                s@.to_multiset() == sorted@.to_multiset(),
                forall|k: int, l: int| 0 <= k < l < i ==> digits_sum(sorted@[k] as int) <= digits_sum(sorted@[l] as int),
                forall|k: int, l: int| 0 <= k < i && i <= l < sorted@.len() ==> digits_sum(sorted@[k] as int) <= digits_sum(sorted@[l] as int),
                i < n,
                j <= n,
                forall|k: int| i < k < j ==> digits_sum(sorted@[i as int] as int) <= digits_sum(sorted@[k] as int),
            decreases n - j
        {
            if exec_digits_sum(sorted[j]) < exec_digits_sum(sorted[i]) {
                let temp = sorted[i];
                sorted.set(i, sorted[j]);
                sorted.set(j, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}