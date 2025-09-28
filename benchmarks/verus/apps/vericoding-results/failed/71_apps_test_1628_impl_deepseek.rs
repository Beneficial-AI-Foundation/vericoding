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

proof fn lemma_filter_preserves_count_char(s: Seq<char>, c: char, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        count_char(s.subrange(0, i), c) == s.subrange(0, i).filter(|x: char| x == c).len()
{
    if i == 0 {
        assert(s.subrange(0, 0).filter(|x: char| x == c).len() == 0);
        assert(count_char(s.subrange(0, 0), c) == 0);
    } else {
        lemma_filter_preserves_count_char(s.subrange(0, i - 1), c, i - 1);
        let prev_count = count_char(s.subrange(0, i - 1), c);
        let prev_filtered = s.subrange(0, i - 1).filter(|x: char| x == c).len();
        assert(prev_count == prev_filtered);
        
        if s[i - 1] == c {
            assert(count_char(s.subrange(0, i), c) == prev_count + 1);
            assert(s.subrange(0, i).filter(|x: char| x == c).len() == prev_filtered + 1);
        } else {
            assert(count_char(s.subrange(0, i), c) == prev_count);
            assert(s.subrange(0, i).filter(|x: char| x == c).len() == prev_filtered);
        }
    }
}

proof fn lemma_sequence_equality_through_filter(s1: Seq<char>, s2: Seq<char>, c: char)
    requires
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() ==> (s1[i] == c) == (s2[i] == c)
    ensures count_char(s1, c) == count_char(s2, c)
{
    assert(s1.filter(|x: char| x == c).len() == s2.filter(|x: char| x == c).len());
}

proof fn lemma_count_char_append(s1: Seq<char>, s2: Seq<char>, c: char)
    ensures count_char(s1 + s2, c) == count_char(s1, c) + count_char(s2, c)
{
    assert((s1 + s2).filter(|x: char| x == c).len() == s1.filter(|x: char| x == c).len() + s2.filter(|x: char| x == c).len());
}

proof fn lemma_subrange_filter_property(s: Seq<char>, start: int, end: int, c: char)
    requires 0 <= start <= end <= s.len()
    ensures count_char(s.subrange(start, end), c) + count_char(s.subrange(end, s.len()), c) == count_char(s.subrange(start, s.len()), c)
{
    lemma_count_char_append(s.subrange(start, end), s.subrange(end, s.len()), c);
    assert(s.subrange(start, end) + s.subrange(end, s.len()) == s.subrange(start, s.len()));
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and postcondition verification */
    let mut x_count: nat = 0;
    let mut y_count: nat = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            x_count == count_char(s@.subrange(0, i as int), 'x'),
            y_count == count_char(s@.subrange(0, i as int), 'y')
        decreases s.len() - i
    {
        let c = s[i];
        proof {
            lemma_filter_preserves_count_char(s@, 'x', i as int);
            lemma_filter_preserves_count_char(s@, 'y', i as int);
        }
        if c == 'x' {
            x_count = (x_count + 1) as nat;
        } else if c == 'y' {
            y_count = (y_count + 1) as nat;
        }
        i = i + 1;
    }
    
    let mut result = Vec::new();
    
    if x_count > y_count {
        let diff = x_count - y_count;
        let mut j: nat = 0;
        while j < diff
            invariant
                0 <= j <= diff,
                result@.len() == j,
                forall|k: int| 0 <= k < j ==> result@[k] == 'x'
            decreases diff - j
        {
            result.push('x');
            j = (j + 1) as nat;
        }
    } else if y_count > x_count {
        let diff = y_count - x_count;
        let mut j: nat = 0;
        while j < diff
            invariant
                0 <= j <= diff,
                result@.len() == j,
                forall|k: int| 0 <= k < j ==> result@[k] == 'y'
            decreases diff - j
        {
            result.push('y');
            j = (j + 1) as nat;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}