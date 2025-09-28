// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_binary_string(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1') &&
    (s == seq!['0'] || s[0] == '1')
}

spec fn count_zeros(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0int
    } else { 
        (if s[0] == '0' { 1int } else { 0int }) + count_zeros(s.subrange(1, s.len() as int))
    }
}

spec fn create_zero_seq(n: nat) -> Seq<char> {
    Seq::new(n, |i: int| '0')
}

spec fn is_minimal_form(s: Seq<char>, result: Seq<char>) -> bool {
    (s == seq!['0'] ==> result == seq!['0'])
    &&
    (s != seq!['0'] ==> result == seq!['1'] + create_zero_seq(count_zeros(s) as nat))
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_zeros_bounds(s: Seq<char>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1',
    ensures
        0 <= count_zeros(s) <= s.len(),
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.subrange(1, s.len() as int).len() == 0);
        assert(count_zeros(s.subrange(1, s.len() as int)) == 0);
    } else {
        lemma_count_zeros_bounds(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_create_zero_seq_properties(n: nat)
    ensures
        create_zero_seq(n).len() == n,
        forall|i: int| 0 <= i < n ==> create_zero_seq(n)[i] == '0',
{
    assert forall|i: int| 0 <= i < n implies create_zero_seq(n)[i] == '0' by {
        assert(create_zero_seq(n)[i] == '0');
    }
}

proof fn lemma_single_zero_string(s: Seq<char>)
    requires
        valid_binary_string(s),
        s == seq!['0'],
    ensures
        count_zeros(s) == 1,
{
    assert(s.len() == 1);
    assert(s[0] == '0');
    assert(s.subrange(1, s.len() as int).len() == 0);
    assert(count_zeros(s) == 1 + count_zeros(s.subrange(1, s.len() as int)));
    assert(count_zeros(s.subrange(1, s.len() as int)) == 0);
}

fn count_zeros_exec(s: &Vec<char>) -> (result: usize)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i] == '0' || s@[i] == '1',
    ensures
        result == count_zeros(s@),
    decreases s.len()
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == count_zeros(s@.subrange(0, i as int)),
            forall|j: int| 0 <= j < s.len() ==> s@[j] == '0' || s@[j] == '1',
        decreases s.len() - i
    {
        proof {
            assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@[i as int]));
            if i == 0 {
                assert(s@.subrange(0, 0) == Seq::empty());
                assert(count_zeros(s@.subrange(0, 0)) == 0);
            }
            let sub_next = s@.subrange(0, (i + 1) as int);
            let sub_curr = s@.subrange(0, i as int);
            assert(sub_next.len() == i + 1);
            assert(sub_next.subrange(1, sub_next.len() as int) == sub_curr);
            if s[i] == '0' {
                assert(sub_next[0] == '0');
                assert(count_zeros(sub_next) == 1 + count_zeros(sub_next.subrange(1, sub_next.len() as int)));
                assert(count_zeros(sub_next) == 1 + count_zeros(sub_curr));
            } else {
                assert(sub_next[0] == '1');
                assert(count_zeros(sub_next) == 0 + count_zeros(sub_next.subrange(1, sub_next.len() as int)));
                assert(count_zeros(sub_next) == count_zeros(sub_curr));
            }
        }
        
        if s[i] == '0' {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s.len() as int) == s@);
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, s: Vec<char>) -> (result: Vec<char>)
    requires 
        n >= 1 && n <= 100,
        s.len() == n as usize,
        valid_binary_string(s@),
    ensures 
        valid_binary_string(result@),
        is_minimal_form(s@, result@),
// </vc-spec>
// <vc-code>
{
    if s.len() == 1 && s[0] == '0' {
        proof {
            lemma_single_zero_string(s@);
            assert(count_zeros(s@) == 1);
            assert(is_minimal_form(s@, seq!['0']));
        }
        return vec!['0'];
    }
    
    proof {
        lemma_count_zeros_bounds(s@);
    }
    
    let zero_count = count_zeros_exec(&s);
    
    let mut result = Vec::new();
    result.push('1');
    
    let mut i: usize = 0;
    while i < zero_count
        invariant
            i <= zero_count,
            zero_count == count_zeros(s@),
            result.len() == i + 1,
            result@[0] == '1',
            forall|j: int| 1 <= j < result.len() ==> result@[j] == '0',
            result@ == seq!['1'] + create_zero_seq(i as nat),
        decreases zero_count - i
    {
        proof {
            lemma_create_zero_seq_properties((i + 1) as nat);
            assert(create_zero_seq((i + 1) as nat) == create_zero_seq(i as nat).push('0'));
        }
        result.push('0');
        i = i + 1;
    }
    
    proof {
        lemma_create_zero_seq_properties(zero_count as nat);
        assert(result@ == seq!['1'] + create_zero_seq(count_zeros(s@) as nat));
        assert(s@ != seq!['0']);
        assert(is_minimal_form(s@, result@));
        assert(valid_binary_string(result@));
    }
    
    result
}
// </vc-code>


}

fn main() {}