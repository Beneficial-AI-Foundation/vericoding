// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 3 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'o' || s[i] == 'x'
}

spec fn count_o(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if s[0] == 'o' { 1int } else { 0int }) + count_o(s.subrange(1, s.len() as int))
    }
}

spec fn calculate_price(s: Seq<char>) -> int
    recommends valid_input(s)
{
    count_o(s) * 100int + 700int
}

spec fn int_to_string_spec(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 {
        seq!['0']
    } else {
        int_to_string_helper_spec(n, seq![])
    }
}

spec fn int_to_string_helper_spec(n: int, acc: Seq<char>) -> Seq<char>
    recommends n >= 0
    decreases n
    when n >= 0
{
    if n == 0 {
        acc
    } else {
        int_to_string_helper_spec(n / 10, seq![((n % 10) + 48) as char] + acc)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed type annotations for c0, c1, c2 and array indexing */
proof fn lemma_count_o_bounds(s: Seq<char>)
    requires
        valid_input(s)
    ensures
        0 <= count_o(s) <= 3
{
    // For a valid input, s.len() == 3, so we need to manually prove the bound
    assert(s.len() == 3);
    let c0: int = if s[0] == 'o' { 1 } else { 0 };
    let c1: int = if s[1] == 'o' { 1 } else { 0 };
    let c2: int = if s[2] == 'o' { 1 } else { 0 };
    assert(count_o(seq![s[2]]) == c2);
    assert(count_o(seq![s[1], s[2]]) == c1 + c2);
    assert(count_o(s) == c0 + c1 + c2);
    assert(0 <= c0 <= 1);
    assert(0 <= c1 <= 1);
    assert(0 <= c2 <= 1);
    assert(0 <= count_o(s) <= 3);
}

fn int_to_string(n: u32) -> (result: Vec<char>)
    ensures
        result@ == int_to_string_spec(n as int)
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        int_to_string_helper(n, Vec::new())
    }
}

/* helper modified by LLM (iteration 4): Fixed precondition handling for n == 0 case */
fn int_to_string_helper(n: u32, acc: Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == int_to_string_helper_spec(n as int, acc@)
    decreases n
{
    if n == 0 {
        acc
    } else {
        let digit = (n % 10 + 48) as u8 as char;
        let mut new_acc = Vec::new();
        new_acc.push(digit);
        let mut i = 0;
        while i < acc.len()
            invariant
                0 <= i <= acc.len(),
                new_acc@.len() == i + 1,
                new_acc@[0] == digit,
                forall|j: int| 0 < j <= i ==> new_acc@[j] == acc@[j - 1]
            decreases acc.len() - i
        {
            new_acc.push(acc[i]);
            i = i + 1;
        }
        assert(new_acc@ == seq![digit] + acc@);
        int_to_string_helper(n / 10, new_acc)
    }
}

/* helper modified by LLM (iteration 4): Fixed index type for accessing s */
fn count_o_exec(s: &Vec<char>) -> (result: u32)
    requires
        valid_input(s@)
    ensures
        result == count_o(s@) as u32
{
    proof {
        lemma_count_o_bounds(s@);
        assert(0 <= count_o(s@) <= 3);
    }
    
    let mut count = 0u32;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s@.len() == 3,
            count == count_o(s@.subrange(0, i as int)) as u32,
            0 <= count_o(s@.subrange(0, i as int)) <= i,
            0 <= count <= 3
        decreases s.len() - i
    {
        proof {
            assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int) + seq![s@[i as int]]);
            if s@[i as int] == 'o' {
                assert(count_o(s@.subrange(0, (i + 1) as int)) == count_o(s@.subrange(0, i as int)) + 1);
            } else {
                assert(count_o(s@.subrange(0, (i + 1) as int)) == count_o(s@.subrange(0, i as int)));
            }
        }
        if s[i] == 'o' {
            count = count + 1;
        }
        i = i + 1;
    }
    assert(s@.subrange(0, s@.len() as int) == s@);
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(s@)
    ensures 
        result@ == int_to_string_spec(calculate_price(s@)) + seq!['\n'],
        calculate_price(s@) >= 700
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added proof for count bounds */
    proof {
        lemma_count_o_bounds(s@);
        assert(0 <= count_o(s@) <= 3);
        assert(calculate_price(s@) == count_o(s@) * 100 + 700);
        assert(calculate_price(s@) >= 700);
    }
    
    let count = count_o_exec(&s);
    let price = count * 100 + 700;
    
    assert(price == calculate_price(s@) as u32);
    
    let mut result = int_to_string(price);
    result.push('\n');
    
    assert(result@ == int_to_string_spec(price as int) + seq!['\n']);
    assert(result@ == int_to_string_spec(calculate_price(s@)) + seq!['\n']);
    
    result
}
// </vc-code>


}

fn main() {}