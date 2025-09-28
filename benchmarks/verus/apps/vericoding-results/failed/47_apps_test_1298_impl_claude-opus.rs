// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] == '0' || #[trigger] s[i] == '1')
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && (s[0] != '0' || s.len() == 1) && forall|i: int| 0 <= i < s.len() ==> ('0' <= #[trigger] s[i] <= '9')
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else { (if s[0] == c { 1int } else { 0int }) + count_char(s.subrange(1, s.len() as int), c) }
}

spec fn abs_diff_count(s: Seq<char>) -> int
    recommends is_binary_string(s)
{
    let count0 = count_char(s, '0');
    let count1 = count_char(s, '1');
    if count1 >= count0 { count1 - count0 } else { count0 - count1 }
}

spec fn int_to_string(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n == 0 { seq!['0'] }
    else if n < 10 { seq![char_of_digit(n)] }
    else { int_to_string(n / 10).add(seq![char_of_digit(n % 10)]) }
}

spec fn char_of_digit(d: int) -> char
    recommends 0 <= d <= 9
{
    if d == 0int { '0' }
    else if d == 1int { '1' }
    else if d == 2int { '2' }
    else if d == 3int { '3' }
    else if d == 4int { '4' }
    else if d == 5int { '5' }
    else if d == 6int { '6' }
    else if d == 7int { '7' }
    else if d == 8int { '8' }
    else if d == 9int { '9' }
    else { '0' }
}

spec fn string_to_int(s: Seq<char>) -> int
    recommends is_valid_integer(s)
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else if s.len() == 1 { (s[0] as int) - ('0' as int) }
    else { string_to_int(s.subrange(0, s.len() - 1)) * 10int + ((s[s.len() - 1] as int) - ('0' as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added trigger annotation to quantifier in int_to_string_valid_integer proof */
proof fn count_char_lemma(s: Seq<char>, c: char, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        count_char(s.subrange(i, s.len() as int), c) >= 0,
    decreases s.len() - i,
{
    if i == s.len() {
        assert(s.subrange(i, s.len() as int).len() == 0);
        assert(count_char(s.subrange(i, s.len() as int), c) == 0);
    } else {
        let sub = s.subrange(i, s.len() as int);
        assert(sub.len() > 0);
        let rest = sub.subrange(1, sub.len() as int);
        assert(rest == s.subrange(i + 1, s.len() as int));
        count_char_lemma(s, c, i + 1);
        assert(count_char(rest, c) >= 0);
        if sub[0] == c {
            assert(count_char(sub, c) == 1 + count_char(rest, c));
        } else {
            assert(count_char(sub, c) == count_char(rest, c));
        }
        assert(count_char(sub, c) >= 0);
    }
}

proof fn count_char_nonnegative(s: Seq<char>, c: char)
    ensures
        count_char(s, c) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        count_char_nonnegative(s.subrange(1, s.len() as int), c);
    }
}

fn compute_count_char(s: &Vec<char>, c: char) -> (count: usize)
    ensures
        count as int == count_char(s@, c),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_char(s@.subrange(0, i as int), c),
            count_char(s@.subrange(0, i as int), c) >= 0,
            count <= i,
        decreases s.len() - i
    {
        proof {
            assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@[i as int]));
            if s@[i as int] == c {
                assert(count_char(s@.subrange(0, (i + 1) as int), c) == count_char(s@.subrange(0, i as int), c) + 1);
                assert(count < i + 1);
            } else {
                assert(count_char(s@.subrange(0, (i + 1) as int), c) == count_char(s@.subrange(0, i as int), c));
                assert(count <= i + 1);
            }
        }
        
        if s[i] == c {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) == s@);
    }
    
    count
}

fn compute_abs_diff(s: &Vec<char>) -> (diff: usize)
    requires
        is_binary_string(s@),
    ensures
        diff as int == abs_diff_count(s@),
{
    let count0 = compute_count_char(s, '0');
    let count1 = compute_count_char(s, '1');
    
    proof {
        count_char_nonnegative(s@, '0');
        count_char_nonnegative(s@, '1');
    }
    
    if count1 >= count0 {
        count1 - count0
    } else {
        count0 - count1
    }
}

proof fn int_to_string_valid_integer(n: int)
    requires
        n >= 0,
    ensures
        is_valid_integer(int_to_string(n)),
    decreases n,
{
    if n == 0 {
        assert(int_to_string(0) == seq!['0']);
        assert(is_valid_integer(seq!['0']));
    } else if n < 10 {
        assert(int_to_string(n) == seq![char_of_digit(n)]);
        assert('0' <= char_of_digit(n) <= '9');
        assert(char_of_digit(n) != '0');
        assert(is_valid_integer(seq![char_of_digit(n)]));
    } else {
        int_to_string_valid_integer(n / 10);
        assert(is_valid_integer(int_to_string(n / 10)));
        let s = int_to_string(n);
        assert(s == int_to_string(n / 10).add(seq![char_of_digit(n % 10)]));
        assert(s.len() > 0);
        assert(s[0] == int_to_string(n / 10)[0]);
        assert(int_to_string(n / 10)[0] != '0' || int_to_string(n / 10).len() == 1);
        assert(n / 10 > 0);
        assert(int_to_string(n / 10)[0] != '0');
        assert(s[0] != '0');
        assert('0' <= char_of_digit(n % 10) <= '9');
        assert(forall|i: int| 0 <= i < s.len() ==> '0' <= #[trigger] s[i] <= '9');
        assert(is_valid_integer(s));
    }
}

fn int_to_vec(n: usize) -> (v: Vec<char>)
    ensures
        v@ == int_to_string(n as int),
        is_valid_integer(v@),
    decreases n,
{
    proof {
        int_to_string_valid_integer(n as int);
    }
    
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        proof {
            assert(v@ == seq!['0']);
            assert(v@ == int_to_string(0));
            assert(is_valid_integer(v@));
        }
        v
    } else if n < 10 {
        let mut v = Vec::new();
        let d = if n == 1 { '1' }
            else if n == 2 { '2' }
            else if n == 3 { '3' }
            else if n == 4 { '4' }
            else if n == 5 { '5' }
            else if n == 6 { '6' }
            else if n == 7 { '7' }
            else if n == 8 { '8' }
            else { '9' };
        v.push(d);
        proof {
            assert(n == 1 ==> d == '1');
            assert(n == 2 ==> d == '2');
            assert(n == 3 ==> d == '3');
            assert(n == 4 ==> d == '4');
            assert(n == 5 ==> d == '5');
            assert(n == 6 ==> d == '6');
            assert(n == 7 ==> d == '7');
            assert(n == 8 ==> d == '8');
            assert(n == 9 ==> d == '9');
            assert(d == char_of_digit(n as int));
            assert(v@ == seq![char_of_digit(n as int)]);
            assert(v@ == int_to_string(n as int));
            assert(is_valid_integer(v@));
        }
        v
    } else {
        let mut v = int_to_vec(n / 10);
        let r = n % 10;
        let d = if r == 0 { '0' }
            else if r == 1 { '1' }
            else if r == 2 { '2' }
            else if r == 3 { '3' }
            else if r == 4 { '4' }
            else if r == 5 { '5' }
            else if r == 6 { '6' }
            else if r == 7 { '7' }
            else if r == 8 { '8' }
            else { '9' };
        v.push(d);
        proof {
            assert(d == char_of_digit((n % 10) as int));
            assert(v@ == int_to_string((n / 10) as int).add(seq![char_of_digit((n % 10) as int)]));
            assert(v@ == int_to_string(n as int));
            assert(is_valid_integer(v@));
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires 
        stdin_input@.len() > 0,
        exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n',
        exists|newline_pos: int| {
            0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
            newline_pos + 1 < stdin_input@.len() &&
            exists|binary_end: int| {
                newline_pos + 1 <= binary_end <= stdin_input@.len() &&
                (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
                is_valid_integer(stdin_input@.subrange(0, newline_pos)) &&
                is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end))
            }
        },
    ensures 
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        exists|newline_pos: int| {
            0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
            newline_pos + 1 < stdin_input@.len() &&
            exists|binary_end: int| {
                newline_pos + 1 <= binary_end <= stdin_input@.len() &&
                (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
                is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end)) &&
                result@ == int_to_string(abs_diff_count(stdin_input@.subrange(newline_pos + 1, binary_end))).add(seq!['\n'])
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed to main solve function */
    let ghost newline_pos_spec: int = choose|newline_pos: int| {
        0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
        newline_pos + 1 < stdin_input@.len() &&
        exists|binary_end: int| {
            newline_pos + 1 <= binary_end <= stdin_input@.len() &&
            (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
            is_valid_integer(stdin_input@.subrange(0, newline_pos)) &&
            is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end))
        }
    };
    
    let ghost binary_end_spec: int = choose|binary_end: int| {
        newline_pos_spec + 1 <= binary_end <= stdin_input@.len() &&
        (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
        is_valid_integer(stdin_input@.subrange(0, newline_pos_spec)) &&
        is_binary_string(stdin_input@.subrange(newline_pos_spec + 1, binary_end))
    };
    
    let mut newline_pos: usize = 0;
    
    while newline_pos < stdin_input.len()
        invariant
            0 <= newline_pos <= stdin_input.len(),
            forall|j: int| 0 <= j < newline_pos ==> stdin_input@[j] != '\n',
            exists|i: int| newline_pos <= i < stdin_input@.len() && stdin_input@[i] == '\n',
            newline_pos <= newline_pos_spec,
        decreases stdin_input.len() - newline_pos
    {
        if stdin_input[newline_pos] == '\n' {
            proof {
                assert(stdin_input@[newline_pos as int] == '\n');
                assert(newline_pos as int == newline_pos_spec);
            }
            break;
        }
        newline_pos = newline_pos + 1;
    }
    
    proof {
        assert(stdin_input@[newline_pos as int] == '\n');
        assert(newline_pos as int == newline_pos_spec);
    }
    
    let mut binary_end: usize = newline_pos + 1;
    
    while binary_end < stdin_input.len() && stdin_input[binary_end] != '\n'
        invariant
            newline_pos + 1 <= binary_end <= stdin_input.len(),
            forall|j: int| newline_pos + 1 <= j < binary_end ==> stdin_input@[j] != '\n',
            binary_end <= binary_end_spec,
        decreases stdin_input.len() - binary_end
    {
        binary_end = binary_end + 1;
    }
    
    proof {
        assert(binary_end as int == binary_end_spec);
    }
    
    let mut binary_string = Vec::new();
    let mut i: usize = newline_pos + 1;
    
    proof {
        assert(is_binary_string(stdin_input@.subrange((newline_pos + 1) as int, binary_end as int)));
    }
    
    while i < binary_end
        invariant
            newline_pos + 1 <= i <= binary_end,
            binary_end <= stdin_input.len(),
            binary_string@ == stdin_input@.subrange((newline_pos + 1) as int, i as int),
            is_binary_string(stdin_input@.subrange((newline_pos + 1) as int, binary_end as int)),
            forall|j: int| (newline_pos + 1) as int <= j < i ==> 
                stdin_input@[j] == '0' || stdin_input@[j] == '1',
            is_binary_string(binary_string@),
        decreases binary_end - i
    {
        proof {
            assert(i < stdin_input.len());
            assert((newline_pos + 1) as int <= i < binary_end);
            assert(stdin_input@[i as int] == '0' || stdin_input@[i as int] == '1');
        }
        binary_string.push(stdin_input[i]);
        proof {
            assert(binary_string@[binary_string@.len() - 1] == stdin_input@[i as int]);
            assert(binary_string@[binary_string@.len() - 1] == '0' || binary_string@[binary_string@.len() - 1] == '1');
            assert(is_binary_string(binary_string@));
        }
        i = i + 1;
    }
    
    assert(binary_string@ == stdin_input@.subrange((newline_pos + 1) as int, binary_end as int));
    
    let diff = compute_abs_diff(&binary_string);
    let mut result = int_to_vec(diff);
    result.push('\n');
    
    proof {
        assert(result@ == int_to_string(diff as int).add(seq!['\n']));
        assert(diff as int == abs_diff_count(stdin_input@.subrange((newline_pos + 1) as int, binary_end as int)));
        assert(newline_pos as int == newline_pos_spec);
        assert(binary_end as int == binary_end_spec);
    }
    
    result
}
// </vc-code>


}
fn main() {}