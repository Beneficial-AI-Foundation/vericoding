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
/* helper modified by LLM (iteration 5): spec mapping from index to desired integer value */
spec fn val_int(i: int) -> int
  requires
      i >= 0,
{
  if i == 0 { 1 }
  else if i == 1 { 2 }
  else if i == 2 { 3 }
  else if i == 3 { 4 }
  else if i == 4 { 5 }
  else if i == 5 { 6 }
  else if i == 6 { 7 }
  else if i == 7 { 8 }
  else if i == 8 { 9 }
  else if i == 9 { 19 }
  else { 19 + (i - 9) }
}
// </vc-helpers>

// <vc-spec>
fn solve(k: i8) -> (result: Vec<i8>)
  requires k as int >= 1
  ensures valid_output(result@.map(|i: int, x: i8| x as int), k as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build result and prove it matches the spec val_int sequence */
  let ki: i32 = k as i32;
  let mut res: Vec<i8> = Vec::new();
  let mut i: i32 = 0;
  while i < ki
      invariant
          res.len() as int == i as int,
          (forall|j: int| 0 <= j < i as int ==> (res@.index(j) as int) == val_int(j)),
      decreases
          (ki - i) as int
  {
      let v_i32: i32 = if i == 0 { 1 }
          else if i == 1 { 2 }
          else if i == 2 { 3 }
          else if i == 3 { 4 }
          else if i == 4 { 5 }
          else if i == 5 { 6 }
          else if i == 6 { 7 }
          else if i == 7 { 8 }
          else if i == 8 { 9 }
          else if i == 9 { 19 }
          else { 19 + (i - 9) };
      let v: i8 = #[verifier::truncate] (v_i32 as i8);
      res.push(v);
      proof {
          if i as int <= 8 {
              if i == 0 { assert(val_int(i as int) == 1); }
              else if i == 1 { assert(val_int(i as int) == 2); }
              else if i == 2 { assert(val_int(i as int) == 3); }
              else if i == 3 { assert(val_int(i as int) == 4); }
              else if i == 4 { assert(val_int(i as int) == 5); }
              else if i == 5 { assert(val_int(i as int) == 6); }
              else if i == 6 { assert(val_int(i as int) == 7); }
              else if i == 7 { assert(val_int(i as int) == 8); }
              else { assert(val_int(i as int) == 9); }
          } else if i as int == 9 {
              assert(val_int(i as int) == 19);
          } else {
              assert(val_int(i as int) == 19 + (i as int - 9));
          }
          assert((res@.index(i as int) as int) == val_int(i as int));
      }
      i = i + 1;
  }
  proof {
      assert(res.len() as int == k as int);
      assert((forall|j: int| 0 <= j < k as int ==> (res@.index(j) as int) == val_int(j)));
      assert(valid_output(res@.map(|_idx: int, x: i8| x as int), k as int));
  }
  res
}
// </vc-code>


}

fn main() {}