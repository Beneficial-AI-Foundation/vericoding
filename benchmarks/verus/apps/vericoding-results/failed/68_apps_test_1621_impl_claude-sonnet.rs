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
/* helper modified by LLM (iteration 5): fix type casting for nat to int */
proof fn lemma_string_value_bounds(s: Seq<char>, w: Seq<int>)
    requires
        w.len() == 26,
        (forall|i: int| 0 <= i < w.len() ==> w[i] >= 0 && w[i] <= 1000),
        (forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] && s[i] <= 'z'),
        s.len() <= 1000
    ensures
        string_value(s, w) >= 0,
        string_value(s, w) <= s.len() * 1000 * 1000
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_string_value_bounds(s.drop_last(), w);
    }
}

proof fn lemma_append_value_bounds(start_pos: int, count: int, max_val: int)
    requires
        start_pos >= 0,
        count >= 0,
        max_val >= 0,
        start_pos <= 1000,
        count <= 1000,
        max_val <= 1000
    ensures
        append_value(start_pos, count, max_val) >= 0,
        append_value(start_pos, count, max_val) <= count * (start_pos + count + 1) * max_val
    decreases count
{
    if count <= 0 {
    } else {
        lemma_append_value_bounds(start_pos, count - 1, max_val);
    }
}

proof fn lemma_max_value_bounds(w: Seq<int>)
    requires
        w.len() == 26,
        (forall|i: int| 0 <= i < w.len() ==> w[i] >= 0 && w[i] <= 1000)
    ensures
        max_value(w) >= 0,
        max_value(w) <= 1000
    decreases w.len()
{
    if w.len() <= 1 {
    } else {
        lemma_max_value_bounds(w.subrange(1, w.len() as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8, w: Vec<i8>) -> (result: i8)
  requires valid_input(s@, k as int, w@.map(|i, x| x as int))
  ensures result as int == string_value(s@, w@.map(|i, x| x as int)) + append_value(s@.len() as int, k as int, max_value(w@.map(|i, x| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix byte literal compilation error */
    proof {
        let mapped_w = w@.map(|i, x| x as int);
        lemma_string_value_bounds(s@, mapped_w);
        lemma_max_value_bounds(mapped_w);
        lemma_append_value_bounds(s@.len() as int, k as int, max_value(mapped_w));
    }
    
    let mut string_val: i32 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            string_val == string_value(s@.subrange(0, i as int), w@.map(|i, x| x as int))
    {
        let char_index = (s[i] as u8 - ('a' as u8)) as usize;
        string_val = string_val + (i as i32 + 1) * (w[char_index] as i32);
        i = i + 1;
    }
    
    let mut append_val: i32 = 0;
    let mut j = 1;
    let max_w = {
        let mut max_val = w[0];
        let mut idx = 1;
        while idx < 26
            invariant
                1 <= idx <= 26,
                max_val >= 0,
                max_val <= 1000,
                (forall|k: int| 0 <= k < idx ==> w@[k] as int <= max_val as int)
        {
            if w[idx] > max_val {
                max_val = w[idx];
            }
            idx = idx + 1;
        }
        max_val
    };
    
    while j <= k
        invariant
            1 <= j <= k + 1,
            append_val == append_value(s@.len() as int, j as int - 1, max_w as int)
    {
        append_val = append_val + (s.len() as i32 + j as i32) * (max_w as i32);
        j = j + 1;
    }
    
    (string_val + append_val) as i8
}
// </vc-code>


}

fn main() {}