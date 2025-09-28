// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'x' || s[i] == 'y'
}

spec fn count_char(s: Seq<char>, c: char) -> nat {
    s.filter(|x: char| x == c).len()
}

spec fn valid_output(s: Seq<char>, result: Seq<char>) -> bool 
    recommends valid_input(s)
{
    let count_x = count_char(s, 'x');
    let count_y = count_char(s, 'y');
    if count_y > count_x {
        result.len() == count_y - count_x && forall|i: int| 0 <= i < result.len() ==> result[i] == 'y'
    } else {
        result.len() == count_x - count_y && forall|i: int| 0 <= i < result.len() ==> result[i] == 'x'
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added lemma to prove count_char increments correctly */
proof fn lemma_count_char_extend(s: Seq<char>, i: int, c: char)
    requires
        0 <= i < s.len(),
    ensures
        count_char(s.subrange(0, i + 1), c) == 
            if s[i] == c { count_char(s.subrange(0, i), c) + 1 }
            else { count_char(s.subrange(0, i), c) },
{
    let s_before = s.subrange(0, i);
    let s_after = s.subrange(0, i + 1);
    assert(s_after =~= s_before.push(s[i]));
    
    let filtered_before = s_before.filter(|x: char| x == c);
    let filtered_after = s_after.filter(|x: char| x == c);
    
    if s[i] == c {
        assert(filtered_after =~= filtered_before.push(s[i]));
        assert(filtered_after.len() == filtered_before.len() + 1);
    } else {
        assert(filtered_after =~= filtered_before);
        assert(filtered_after.len() == filtered_before.len());
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed indexing to use i as int for s@ */
    let mut count_x: usize = 0;
    let mut count_y: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count_x == count_char(s@.subrange(0, i as int), 'x'),
            count_y == count_char(s@.subrange(0, i as int), 'y'),
        decreases s.len() - i
    {
        let old_count_x = count_x;
        let old_count_y = count_y;
        
        if s@[i as int] == 'x' {
            count_x = count_x + 1;
        } else {
            count_y = count_y + 1;
        }
        
        proof {
            lemma_count_char_extend(s@, i as int, 'x');
            lemma_count_char_extend(s@, i as int, 'y');
            
            if s@[i as int] == 'x' {
                assert(count_char(s@.subrange(0, (i + 1) as int), 'x') == old_count_x + 1);
                assert(count_char(s@.subrange(0, (i + 1) as int), 'y') == old_count_y);
            } else {
                assert(s@[i as int] == 'y');  // from valid_input
                assert(count_char(s@.subrange(0, (i + 1) as int), 'x') == old_count_x);
                assert(count_char(s@.subrange(0, (i + 1) as int), 'y') == old_count_y + 1);
            }
        }
        
        i = i + 1;
    }
    
    assert(s@.subrange(0, s.len() as int) == s@);
    assert(count_x == count_char(s@, 'x'));
    assert(count_y == count_char(s@, 'y'));
    
    let mut result = Vec::new();
    
    if count_y > count_x {
        let diff = count_y - count_x;
        let mut j: usize = 0;
        while j < diff
            invariant
                0 <= j <= diff,
                result.len() == j,
                forall|k: int| 0 <= k < j ==> result@[k] == 'y',
            decreases diff - j
        {
            result.push('y');
            j = j + 1;
        }
    } else {
        let diff = count_x - count_y;
        let mut j: usize = 0;
        while j < diff
            invariant
                0 <= j <= diff,
                result.len() == j,
                forall|k: int| 0 <= k < j ==> result@[k] == 'x',
            decreases diff - j
        {
            result.push('x');
            j = j + 1;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}