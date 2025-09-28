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
proof fn lemma_max_value_range_26(w: Seq<int>)
    requires
        w.len() == 26,
        forall|i: int| 0 <= i < w.len() ==> #[trigger] w[i] >= 0
    ensures
        max_value(w) >= 0
{
    lemma_max_value_nonnegative(w);
}

proof fn lemma_append_value_recursive(start_pos: int, count: int, max_val: int)
    requires
        start_pos >= 0,
        count >= 0,
        max_val >= 0
    ensures
        append_value(start_pos, count, max_val) >= 0,
        count <= 0 ==> append_value(start_pos, count, max_val) == 0,
        count > 0 ==> append_value(start_pos, count, max_val) == (start_pos + count) * max_val + append_value(start_pos, count - 1, max_val)
{
    if count <= 0 {
        assert(append_value(start_pos, count, max_val) == 0);
    } else {
        lemma_append_value_recursive(start_pos, count - 1, max_val);
    }
}

proof fn lemma_char_inside(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        forall|j: int| 0 <= j < s.len() ==> 'a' <= #[trigger] s[j] && #[trigger] s[j] <= 'z'
    ensures
        'a' <= s[i] <= 'z',
        (s[i] as int) - ('a' as int) >= 0,
        (s[i] as int) - ('a' as int) < 26
{
    assert('a' as int <= s[i] as int <= 'z' as int);
    assert((s[i] as int) - ('a' as int) >= 0);
    assert((s[i] as int) - ('a' as int) < 26);
}

fn find_max(w: Vec<i8>) -> (max_val: i8)
    requires w.len() == 26
    ensures 
        max_val >= 0,
        forall|i: int| 0 <= i < w.len() ==> w[i] <= max_val
{
    let mut max_val = w[0];
    let mut j = 1;
    
    while j < w.len()
        invariant
            j <= w.len(),
            max_val >= 0,
            forall|k: int| 0 <= k < j ==> w[k] <= max_val
        decreases w.len() - j
    {
        if w[j] > max_val {
            max_val = w[j];
        }
        j += 1;
    }
    
    max_val
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8, w: Vec<i8>) -> (result: i8)
  requires valid_input(s@, k as int, w@.map(|i, x| x as int))
  ensures result as int == string_value(s@, w@.map(|i, x| x as int)) + append_value(s@.len() as int, k as int, max_value(w@.map(|i, x| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed bounds checking, char index calculation, and out of bounds issues */
    let mut result: i8 = 0;
    let mut i: usize = 0;
    let s_len = s.len();
    
    proof {
        lemma_max_value_range_26(w@.map(|i, x| x as int));
    }
    
    while i < s_len
        invariant
            i <= s_len,
            result as int == string_value(s@.subrange(0, i as int), w@.map(|idx, x| x as int)),
            forall|j: int| i <= j < s_len ==> 'a' <= s@[j] <= 'z'
        decreases s_len - i
    {
        proof {
            lemma_char_inside(s@, i as int);
        }
        
        let char_val = s[i];
        let char_index = (char_val as u32 - 'a' as u32) as usize;
        let weight = w[char_index];
        result = ((result as i32) + ((i + 1) as i32 * weight as i32)) as i8;
        i += 1;
    }
    
    let max_val = find_max(w);
    
    let mut append_sum: i32 = 0;
    let mut count: i32 = 0;
    let k_i32 = k as i32;
    let s_len_i32 = s_len as i32;
    let max_val_i32 = max_val as i32;
    
    proof {
        lemma_append_value_recursive(s_len_i32, k_i32, max_val_i32);
    }
    
    while count < k_i32
        invariant
            count <= k_i32,
            append_sum as int == append_value(s_len_i32 as int, count as int, max_val_i32 as int)
        decreases k_i32 - count
    {
        append_sum += (s_len_i32 + count + 1) * max_val_i32;
        count += 1;
    }
    
    ((result as i32) + append_sum) as i8
}
// </vc-code>


}

fn main() {}