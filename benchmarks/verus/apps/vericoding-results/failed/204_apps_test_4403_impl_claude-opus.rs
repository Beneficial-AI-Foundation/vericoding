// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 4 && forall|i: int| 0 <= i < s.len() ==> s[i] == '+' || s[i] == '-'
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0nat as int
    } else {
        (if s[0] == c { 1nat as int } else { 0nat as int }) + count_char(s.subrange(1, s.len() as int), c)
    }
}

spec fn calculate_sum(s: Seq<char>) -> int {
    count_char(s, '+') - count_char(s, '-')
}
// </vc-preamble>

// <vc-helpers>
proof fn count_char_empty(c: char)
    ensures count_char(Seq::<char>::empty(), c) == 0
{
}

/* helper modified by LLM (iteration 5): Fixed proof to match recursive definition */
proof fn count_char_single(s: Seq<char>, c: char)
    requires s.len() == 1
    ensures count_char(s, c) == if s[0] == c { 1int } else { 0int }
{
    assert(s.subrange(1, s.len() as int) =~= Seq::<char>::empty());
    assert(count_char(s.subrange(1, s.len() as int), c) == 0);
}

/* helper modified by LLM (iteration 5): Complete inductive proof for split property */
proof fn count_char_split(s: Seq<char>, c: char, i: int)
    requires 0 <= i <= s.len()
    ensures count_char(s, c) == count_char(s.subrange(0, i), c) + count_char(s.subrange(i, s.len() as int), c)
    decreases s.len(), i
{
    if s.len() == 0 {
        assert(s.subrange(0, i) =~= Seq::<char>::empty());
        assert(s.subrange(i, s.len() as int) =~= Seq::<char>::empty());
    } else if i == 0 {
        assert(s.subrange(0, i) =~= Seq::<char>::empty());
        assert(s.subrange(i, s.len() as int) =~= s);
    } else {
        let first_char = if s[0] == c { 1int } else { 0int };
        let rest = s.subrange(1, s.len() as int);
        
        count_char_split(rest, c, i - 1);
        
        assert(s.subrange(0, i) =~= seq![s[0]] + rest.subrange(0, i - 1));
        assert(s.subrange(i, s.len() as int) =~= rest.subrange(i - 1, rest.len() as int));
        assert(count_char(s.subrange(0, i), c) == first_char + count_char(rest.subrange(0, i - 1), c));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == calculate_sum(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat literal syntax and casting */
    let mut plus_count: nat = 0nat;
    let mut minus_count: nat = 0nat;
    let mut i: usize = 0;
    
    while i < 4
        invariant
            i <= 4,
            plus_count == count_char(s@.subrange(0, i as int), '+') as nat,
            minus_count == count_char(s@.subrange(0, i as int), '-') as nat,
            plus_count <= 4,
            minus_count <= 4,
            s@.len() == 4,
            valid_input(s@),
        decreases 4 - i
    {
        proof {
            count_char_split(s@, '+', i as int);
            count_char_split(s@, '-', i as int);
            
            let prefix = s@.subrange(0, i as int);
            let current = s@.subrange(i as int, (i + 1) as int);
            let full = s@.subrange(0, (i + 1) as int);
            
            assert(current.len() == 1);
            assert(current[0] == s@[i as int]);
            assert(full =~= prefix + current);
            
            count_char_single(current, '+');
            count_char_single(current, '-');
        }
        
        if s[i] == '+' {
            plus_count = plus_count + 1nat;
        } else if s[i] == '-' {
            minus_count = minus_count + 1nat;
        }
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, 4) =~= s@);
        assert(plus_count == count_char(s@, '+') as nat);
        assert(minus_count == count_char(s@, '-') as nat);
    }
    
    let result: i8 = (plus_count as int) as i8 - (minus_count as int) as i8;
    result
}
// </vc-code>


}

fn main() {}