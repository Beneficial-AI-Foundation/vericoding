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
/* helper modified by LLM (iteration 4): Fixed lemma_append_value_sum proof and added helper for max_value */
proof fn lemma_append_value_sum(start_pos: int, count: int, max_val: int)
    ensures
        append_value(start_pos, count, max_val) == 
        if count <= 0 { 0 } 
        else { max_val * count * (2 * start_pos + count + 1) / 2 }
    decreases count
{
    if count <= 0 {
    } else if count == 1 {
        // Base case: append_value(start_pos, 1, max_val) = (start_pos + 1) * max_val
        assert(append_value(start_pos, 1, max_val) == (start_pos + 1) * max_val);
        assert(1 * (2 * start_pos + 1 + 1) / 2 == (2 * start_pos + 2) / 2);
        assert((2 * start_pos + 2) / 2 == start_pos + 1);
    } else {
        lemma_append_value_sum(start_pos, count - 1, max_val);
        // Recursive case
        let sum_prev = (count - 1) * (2 * start_pos + count) / 2;
        let sum_curr = count * (2 * start_pos + count + 1) / 2;
        
        // Need to show: (start_pos + count) + sum_prev == sum_curr
        assert(2 * (start_pos + count) == 2 * start_pos + 2 * count);
        assert(2 * sum_prev == (count - 1) * (2 * start_pos + count));
        assert(2 * sum_curr == count * (2 * start_pos + count + 1));
        assert(2 * sum_curr == count * (2 * start_pos + count) + count);
        assert(2 * sum_curr == (count - 1) * (2 * start_pos + count) + (2 * start_pos + count) + count);
        assert(2 * sum_curr == 2 * sum_prev + 2 * start_pos + 2 * count);
        assert(sum_curr == sum_prev + start_pos + count);
    }
}

proof fn lemma_string_value_computation(s: Seq<char>, w: Seq<int>, i: int)
    requires
        0 <= i <= s.len(),
        w.len() == 26,
        forall|j: int| 0 <= j < s.len() ==> 'a' <= #[trigger] s[j] && #[trigger] s[j] <= 'z'
    ensures
        string_value(s.subrange(0, i), w) == 
        if i == 0 { 0 }
        else { string_value(s.subrange(0, i - 1), w) + i * w[(s[i - 1] as int) - ('a' as int)] }
    decreases i
{
    if i == 0 {
        assert(s.subrange(0, 0).len() == 0);
    } else {
        assert(s.subrange(0, i) =~= s.subrange(0, i - 1).push(s[i - 1]));
        assert(s.subrange(0, i).last() == s[i - 1]);
        assert(s.subrange(0, i).drop_last() =~= s.subrange(0, i - 1));
    }
}

proof fn lemma_max_value_prefix(w: Seq<int>, i: int)
    requires
        1 <= i < w.len(),
        w.len() >= 1
    ensures
        max_value(w.subrange(0, i + 1)) == 
        if w[i] > max_value(w.subrange(0, i)) { w[i] } 
        else { max_value(w.subrange(0, i)) }
{
    if i == 1 {
        assert(w.subrange(0, 2) =~= seq![w[0], w[1]]);
    } else {
        assert(w.subrange(0, i + 1).subrange(1, (i + 1) as int) =~= w.subrange(1, i + 1));
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
    /* code modified by LLM (iteration 4): Fixed overflow issues and character indexing */
    let mut max_w: i8 = w[0];
    let mut i: usize = 1;
    
    while i < w.len()
        invariant
            1 <= i <= w.len(),
            w.len() == 26,
            max_w as int == max_value(w@.map(|j, x| x as int).subrange(0, i as int))
        decreases w.len() - i
    {
        proof {
            lemma_max_value_prefix(w@.map(|j, x| x as int), i as int);
        }
        if w[i] > max_w {
            max_w = w[i];
        }
        i = i + 1;
    }
    
    assert(w@.map(|j, x| x as int).subrange(0, 26) =~= w@.map(|j, x| x as int));
    
    let mut value: i32 = 0;
    let mut j: usize = 0;
    
    while j < s.len()
        invariant
            0 <= j <= s.len(),
            value == string_value(s@.subrange(0, j as int), w@.map(|idx, x| x as int)),
            s.len() <= 1000,
            forall|idx: int| 0 <= idx < j ==> 'a' <= #[trigger] s@[idx] && #[trigger] s@[idx] <= 'z'
        decreases s.len() - j
    {
        // Safe character to index conversion
        assert('a' <= s[j] <= 'z');
        let char_code = s[j] as u8;
        let a_code = 'a' as u8;
        assert(a_code <= char_code);
        let char_val = (char_code - a_code) as usize;
        assert(0 <= char_val < 26);
        
        let j_plus_1 = (j as i32) + 1;
        assert(0 <= j_plus_1 <= 1000);
        value = value + j_plus_1 * (w[char_val] as i32);
        
        proof {
            lemma_string_value_computation(s@, w@.map(|idx, x| x as int), (j + 1) as int);
            assert(s@.subrange(0, (j + 1) as int)[j as int] == s@[j as int]);
        }
        
        j = j + 1;
    }
    
    assert(s@.subrange(0, s@.len() as int) =~= s@);
    
    let mut append_val: i32 = 0;
    let mut count: i8 = k;
    let start_pos = s.len() as i32;
    
    while count > 0
        invariant
            0 <= count <= k,
            append_val == append_value(start_pos as int, (k - count) as int, max_w as int),
            start_pos <= 1000,
            k <= 127
        decreases count
    {
        let k_minus_count = (k as i32) - (count as i32);
        let pos = start_pos + k_minus_count + 1;
        assert(0 <= pos <= 2000);
        append_val = append_val + pos * (max_w as i32);
        count = count - 1;
    }
    
    assert((k - count) as int == k as int);
    assert(value + append_val <= 2000 * 1000 + 1000 * 1000);
    
    (value + append_val) as i8
}
// </vc-code>


}

fn main() {}