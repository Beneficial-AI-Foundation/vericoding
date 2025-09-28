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
/* helper modified by LLM (iteration 5): added named return type to fix compilation error where 'result' was not in scope */
fn compute_max_weight(w: &Vec<i8>) -> (result: i8)
    requires
        w@.len() == 26,
        forall |i: int| 0 <= i < 26 ==> w@[i] as int >= 0 && w@[i] as int <= 1000
    ensures
        result as int == max_value(w@.map(|i, x: i8| x as int))
{
    let mut max_val = w[0];
    for i in 1..26
        invariant
            forall |j: int| 0 <= j < i ==> max_val as int >= w@[j] as int,
            1 <= i <= 26,
            max_val as int >= 0 && max_val as int <= 1000
        decreases 26 - i
    {
        if w[i] > max_val { max_val = w[i]; }
    }
    max_val
}

fn compute_string_value(s: &Vec<char>, w: &Vec<i32>, start: usize, end: usize) -> (result: i32)
    requires
        start <= end && end <= s@.len(),
        w@.len() == 26,
        forall |i: int| start <= i < end ==> 'a' <= s@[i] && s@[i] <= 'z',
        forall |i: int| 0 <= i < 26 ==> 0 <= w@[i] && w@[i] <= 1000
    ensures
        result == string_value(s@.subrange(start as int, end as int), w@.map(|i, x: i32| x as int))
    decreases end - start
{
    if start == end {
        0
    } else {
        let recurse = compute_string_value(s, w, start, end - 1);
        let elem = s[end - 1];
        let char_index = (elem as i32 - 'a' as i32) as usize;
        recurse + ((end - start) as i32) * w[char_index]
    }
}

fn compute_append_value(start_pos: i32, count: i32, max_val: i32) -> (result: i32)
    requires
        count >= 0
    ensures
        result as int == append_value(start_pos as int, count as int, max_val as int)
    decreases count as nat
{
    if count <= 0 {
        0
    } else {
        (start_pos + count) * max_val + compute_append_value(start_pos, count - 1, max_val)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8, w: Vec<i8>) -> (result: i8)
  requires valid_input(s@, k as int, w@.map(|i, x| x as int))
  ensures result as int == string_value(s@, w@.map(|i, x| x as int)) + append_value(s@.len() as int, k as int, max_value(w@.map(|i, x| x as int)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented the main logic using helper functions with converted types and computations */
{
    let w_int: Vec<i32> = w.iter().map(|&x| x as i32).collect();
    let max_w = compute_max_weight(&w);
    let str_val = compute_string_value(&s, &w_int, 0, s.len());
    let start_pos = s.len() as i32;
    let count_ = k as i32;
    let app_val = compute_append_value(start_pos, count_, max_w as i32);
    (str_val + app_val) as i8
}
// </vc-code>


}

fn main() {}