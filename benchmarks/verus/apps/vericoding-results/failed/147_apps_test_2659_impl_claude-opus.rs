// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_of_digits(n: int) -> int
  recommends n >= 0
  decreases n
{
  if n < 10 { n }
  else { (n % 10) + sum_of_digits(n / 10) }
}

spec fn valid_output(result: Seq<int>, k: int) -> bool {
  &&& result.len() == k
  &&& (forall|i: int| 0 <= i < k ==> result[i] > 0)
  &&& (forall|i: int| #![trigger result.index(i)] 0 <= i < k - 1 ==> result.index(i) < result.index(i + 1))
  &&& (k >= 1 ==> result[0] == 1)
  &&& (k >= 2 ==> result[1] == 2)
  &&& (k >= 3 ==> result[2] == 3)
  &&& (k >= 4 ==> result[3] == 4)
  &&& (k >= 5 ==> result[4] == 5)
  &&& (k >= 6 ==> result[5] == 6)
  &&& (k >= 7 ==> result[6] == 7)
  &&& (k >= 8 ==> result[7] == 8)
  &&& (k >= 9 ==> result[8] == 9)
  &&& (k >= 10 ==> result[9] == 19)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(k: i8) -> (result: Vec<i8>)
  requires k as int >= 1
  ensures valid_output(result@.map(|i: int, x: i8| x as int), k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop bounds and invariants for k > 10 */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < k as usize
        invariant
            0 <= i <= k as usize,
            result.len() == i,
            forall|j: int| 0 <= j < i as int && j < 9 ==> result@[j] == (j + 1) as i8,
            i >= 9 && i > 0 ==> result@[8] == 9i8,
            i >= 10 ==> result@[9] == 19i8,
            forall|j: int| 0 <= j < i as int && j >= 10 ==> result@[j] == (19 + (j - 9)) as i8,
            forall|j: int| 0 <= j < i as int ==> result@[j] > 0,
            forall|j: int| 0 <= j < i as int - 1 ==> result@[j] < result@[j + 1],
        decreases (k as usize) - i
    {
        let next_val: i8 = if i < 9 { 
            (i + 1) as i8
        } else if i == 9 {
            19i8
        } else {
            (19 + ((i - 9) as i8))
        };
        result.push(next_val);
        i = i + 1;
    }
    
    assert(result.len() == k as usize);
    assert(forall|j: int| 0 <= j < k as int ==> result@[j] > 0);
    
    result
}
// </vc-code>


}

fn main() {}