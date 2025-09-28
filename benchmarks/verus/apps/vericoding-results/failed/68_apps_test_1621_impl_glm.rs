// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_value(s: Seq<char>, w: Seq<int>) -> int
  decreases s.len()
{
  if s.len() == 0 { 0 }
  else {
    let char_index = (s.last() as int) - ('a' as int);
    string_value(s.drop_last(), w) + s.len() * w[char_index]
  }
}

spec fn append_value(start_pos: int, count: int, max_val: int) -> int
  decreases count
{
  if count <= 0 { 0 }
  else { (start_pos + count) * max_val + append_value(start_pos, count - 1, max_val) }
}

spec fn max_value(w: Seq<int>) -> int
  decreases w.len()
{
  if w.len() <= 1 { w[0] }
  else if w[0] >= max_value(w.subrange(1, w.len() as int)) { w[0] }
  else { max_value(w.subrange(1, w.len() as int)) }
}

spec fn valid_input(s: Seq<char>, k: int, w: Seq<int>) -> bool
{
  w.len() == 26 && 
  k >= 0 && 
  s.len() <= 1000 && 
  k <= 1000 && 
  (forall|i: int| 0 <= i < w.len() ==> #[trigger] w[i] >= 0 && #[trigger] w[i] <= 1000) &&
  (forall|i: int| 0 <= i < s.len() ==> 'a' <= #[trigger] s[i] && #[trigger] s[i] <= 'z')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed to start loop at 0 and use forward iteration for max_value */
fn exec_max_value(w: &Vec<i8>) -> (result: i64)
  requires w@.len() == 26
  ensures result as int == max_value(w@.map(|i, x| x as int))
{
  let mut max = 0;
  let mut i = 0;
  while i < w.len()
    invariant
        0 <= i <= w.len(),
        max as int == max_value(w@.subrange(0, i as int).map(|j, x| x as int)),
    decreases w.len() - i
  {
    if (w[i] as i64) > max {
      max = w[i] as i64;
    }
    i += 1;
  }
  max
}

/* helper modified by LLM (iteration 4): changed to iterate from end to beginning for string_value */
fn exec_string_value(s: &Vec<char>, w: &Vec<i8>) -> (result: i64)
  requires valid_input(s@, 0, w@.map(|i, x| x as int))
  ensures result as int == string_value(s@, w@.map(|j, x| x as int))
{
  let mut total = 0;
  let mut i = s.len() as i64;
  while i > 0
    invariant
        0 <= i <= s.len() as int,
        total as int == string_value(s@.subrange(i as int, s.len() as int), w@.map(|j, x| x as int)),
    decreases i
  {
    i -= 1;
    let c = s[i as usize];
    let char_index = (c as u8 - 'a' as u8) as usize;
    total = total + (i + 1) * (w[char_index] as i64);
  }
  total
}

/* helper modified by LLM (iteration 4): changed to closed-form formula for append_value */
fn exec_append_value(start_pos: i64, count: i64, max_val: i64) -> (result: i64)
  requires count >= 0
  ensures result as int == append_value(start_pos as int, count as int, max_val as int)
{
  if count <= 0 {
    0
  } else {
    let n = count;
    let sum = n * (2 * start_pos + n + 1) / 2;
    max_val * sum
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8, w: Vec<i8>) -> (result: i8)
  requires valid_input(s@, k as int, w@.map(|i, x| x as int))
  ensures result as int == string_value(s@, w@.map(|i, x| x as int)) + append_value(s@.len() as int, k as int, max_value(w@.map(|i, x| x as int)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix placement of verifier::truncate attribute */
{
  let max_val = exec_max_value(&w);
  let string_val = exec_string_value(&s, &w);
  let append_val = exec_append_value(s.len() as i64, k as i64, max_val);
  let total = string_val + append_val;
  (#[verifier::truncate] total) as i8
}
// </vc-code>


}

fn main() {}