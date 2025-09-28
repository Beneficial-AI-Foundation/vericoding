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
/* helper modified by LLM (iteration 5): Fixed lemma_subrange_full to use int type for s.len() */
proof fn lemma_count_char_empty(c: char)
    ensures count_char(seq![], c) == 0nat
{
}

proof fn lemma_count_char_push(s: Seq<char>, x: char, c: char)
    ensures count_char(s.push(x), c) == count_char(s, c) + (if x == c { 1nat } else { 0nat })
{
    assert(s.push(x).filter(|y: char| y == c) =~= s.filter(|y: char| y == c) + if x == c { seq![x] } else { seq![] });
}

proof fn lemma_filter_len_le(s: Seq<char>, c: char)
    ensures count_char(s, c) <= s.len()
{
}

proof fn lemma_subrange_push(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1) == s.subrange(0, i).push(s[i])
{
}

proof fn lemma_subrange_full(s: Seq<char>)
    ensures s.subrange(0, s.len() as int) == s
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed subrange calls to use int type for s.len() */
    let mut count_x: usize = 0;
    let mut count_y: usize = 0;
    
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count_x == count_char(s@.subrange(0, i as int), 'x'),
            count_y == count_char(s@.subrange(0, i as int), 'y'),
        decreases s.len() - i
    {
        proof {
            lemma_subrange_push(s@, i as int);
            lemma_count_char_push(s@.subrange(0, i as int), s@[i as int], 'x');
            lemma_count_char_push(s@.subrange(0, i as int), s@[i as int], 'y');
        }
        
        if s[i] == 'x' {
            count_x += 1;
        } else {
            count_y += 1;
        }
        i += 1;
    }
    
    proof {
        lemma_subrange_full(s@);
    }
    
    let mut result = Vec::new();
    
    if count_y > count_x {
        let diff = count_y - count_x;
        let mut j = 0;
        while j < diff
            invariant
                0 <= j <= diff,
                result.len() == j,
                forall|k: int| 0 <= k < result.len() ==> result@[k] == 'y',
            decreases diff - j
        {
            result.push('y');
            j += 1;
        }
    } else {
        let diff = count_x - count_y;
        let mut j = 0;
        while j < diff
            invariant
                0 <= j <= diff,
                result.len() == j,
                forall|k: int| 0 <= k < result.len() ==> result@[k] == 'x',
            decreases diff - j
        {
            result.push('x');
            j += 1;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}