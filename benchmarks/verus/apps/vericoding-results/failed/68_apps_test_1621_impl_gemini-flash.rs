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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8, w: Vec<i8>) -> (result: i8)
  requires valid_input(s@, k as int, w@.map(|i, x| x as int))
  ensures result as int == string_value(s@, w@.map(|i, x| x as int)) + append_value(s@.len() as int, k as int, max_value(w@.map(|i, x| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors related to `for` loop ranges, sequence indexing, and type casting. Changed `s_seq.len()` to `s.len()` for iteration and `s[i]` for indexing. Adjusted `max_weight` loop to iterate over `w.len()` and ensure `k` is treated as `usize` for the append loop. Cast `start_pos_int` to `usize` for addition. */
    let ghost k_int = k as int;
    let ghost w_seq_int = w@.map(|_i, x| x as int);

    let mut current_value: i32 = 0;
    for i in 0..s.len() {
        let char_val = (s[i] as u8 - b'a') as usize;
        current_value = current_value + ((i + 1) as i32) * (w[char_val] as i32);
    }

    let mut max_weight: i8 = 0;
    if w.len() > 0 {
        max_weight = w[0];
        for i in 1..w.len() {
            if w[i] > max_weight {
                max_weight = w[i];
            }
        }
    }

    let mut append_val: i32 = 0;
    let start_pos_int = s.len();
    for i in 1..=(k as usize) {
        append_val = append_val + ((start_pos_int as usize + i) as i32) * (max_weight as i32);
    }

    (current_value + append_val) as i8
}
// </vc-code>


}

fn main() {}