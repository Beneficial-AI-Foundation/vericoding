// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    (exists|i: int| 0 <= i < stdin_input.len() && stdin_input[i] == '\n') &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let k_str = stdin_input.subrange(0, newline_pos as int);
        is_valid_positive_integer(k_str)
    }) &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let k_str = stdin_input.subrange(0, newline_pos as int);
        let k = string_to_int(k_str);
        1 <= k <= 100
    }) &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let rest = stdin_input.subrange(newline_pos as int + 1, stdin_input.len() as int);
        let s = if rest.len() > 0 && rest[rest.len() - 1] == '\n' { rest.subrange(0, rest.len() - 1) } else { rest };
        1 <= s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
    })
}

spec fn extract_k(stdin_input: Seq<char>) -> int
    recommends valid_input(stdin_input)
{
    let newline_pos = find_newline(stdin_input, 0);
    let k_str = stdin_input.subrange(0, newline_pos as int);
    string_to_int(k_str)
}

spec fn extract_s(stdin_input: Seq<char>) -> Seq<char>
    recommends valid_input(stdin_input)
{
    let newline_pos = find_newline(stdin_input, 0);
    let rest = stdin_input.subrange(newline_pos as int + 1, stdin_input.len() as int);
    if rest.len() > 0 && rest[rest.len() - 1] == '\n' { rest.subrange(0, rest.len() - 1) } else { rest }
}

spec fn correct_output(stdin_input: Seq<char>, result: Seq<char>) -> bool
    recommends valid_input(stdin_input)
{
    let k = extract_k(stdin_input);
    let s = extract_s(stdin_input);
    k >= 1 && k <= 100 &&
    s.len() >= 1 && s.len() <= 100 &&
    (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z') &&
    (s.len() <= k ==> result == s.add(seq!['\n'])) &&
    (s.len() > k ==> result == s.subrange(0, k).add(seq!['.', '.', '.']).add(seq!['\n']))
}

spec fn find_newline(s: Seq<char>, start: nat) -> nat
    recommends start <= s.len()
    decreases s.len() - start
{
    if start >= s.len() { 
        s.len() 
    } else if s[start as int] == '\n' { 
        start 
    } else { 
        find_newline(s, start + 1) 
    }
}

spec fn is_valid_positive_integer(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9') && 
    s != seq!['0']
}

spec fn string_to_int(s: Seq<char>) -> int
    recommends is_valid_positive_integer(s)
{
    string_to_int_helper(s, 0, 0)
}

spec fn string_to_int_helper(s: Seq<char>, pos: nat, acc: int) -> int
    recommends
        pos <= s.len(),
        acc >= 0,
        forall|i: int| 0 <= i < pos ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9',
        is_valid_positive_integer(s)
    decreases s.len() - pos
{
    if pos >= s.len() { 
        if acc == 0 { 1 } else { acc }
    } else if s[pos as int] >= '0' && s[pos as int] <= '9' {
        string_to_int_helper(s, pos + 1, acc * 10 + (s[pos as int] as int - '0' as int))
    } else {
        if acc == 0 { 1 } else { acc }
    }
}
// </vc-preamble>

// <vc-helpers>
{
    /* code modified by LLM (iteration 5): runtime parsing of k and s, build result without casting spec nat/int */
    let len = stdin_input.len();
    let view = stdin_input.view();
    proof { assert(len == view.len()); }

    // find newline position at runtime
    let mut i: usize = 0;
    while i < len && stdin_input[i] != '\n'
        invariant
            i <= len,
            forall|j: int| 0 <= j < i ==> view[j] != '\n',
        decreases len - i
    {
        i += 1;
    }
    let newline_pos: usize = i;

    // parse k from chars [0, newline_pos)
    let mut k: usize = 0;
    let mut pidx: usize = 0;
    while pidx < newline_pos
        invariant
            pidx <= newline_pos,
            (k as int) == seq_prefix_to_int(view, pidx),
        decreases newline_pos - pidx
    {
        let ch = stdin_input[pidx];
        // use primitive casts between char->u32 and u32->usize
        let digit = (ch as u32 - '0' as u32) as usize;
        k = k * 10 + digit;
        pidx += 1;
    }

    // build svec from the remainder
    let rest_start = newline_pos + 1;
    proof { assert(rest_start <= len); }
    let mut svec: Vec<char> = Vec::new();
    let mut idx: usize = rest_start;
    while idx < len
        invariant
            rest_start <= idx,
            idx <= len,
            svec.view() == view.subrange(rest_start as int, idx as int),
        decreases len - idx
    {
        svec.push(stdin_input[idx]);
        idx += 1;
    }

    // if trailing newline in the rest, remove it
    if svec.len() > 0 && svec[svec.len() - 1] == '\n' {
        svec.pop();
    }

    // proofs connecting runtime values to specs
    proof {
        // prove runtime newline_pos matches spec find_newline
        find_newline_from(view, 0, newline_pos);
        // prove parsed k matches spec string_to_int on the k substring
        // pidx == newline_pos, and invariant gave k relation for pidx
        assert((k as int) == seq_prefix_to_int(view, newline_pos));
        string_to_int_matches_seq_prefix(view, newline_pos);
        assert((k as int) == string_to_int(view.subrange(0, newline_pos as int)));
        // prove svec corresponds to extract_s(stdin_input@)
        if rest_start <= len {
            if newline_pos < len && view[len as int - 1] == '\n' {
                // handled by pop above; rely on extract_s definition
            }
        }
    }

    // produce result
    if svec.len() <= k {
        svec.push('\n');
        svec
    } else {
        let mut res: Vec<char> = Vec::new();
        let mut q: usize = 0;
        while q < k
            invariant
                q <= k,
                res.len() == q,
            decreases k - q
        {
            res.push(svec[q]);
            q += 1;
        }
        res.push('.');
        res.push('.');
        res.push('.');
        res.push('\n');
        res
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
/* helper modified by LLM (iteration 5): seq_prefix_to_int computes integer value of digit prefix */
spec fn seq_prefix_to_int(s: Seq<char>, pos: nat) -> int
    decreases pos
{
    if pos == 0 {
        0
    } else {
        seq_prefix_to_int(s, pos - 1) * 10 + (s[(pos - 1) as int] as int - '0' as int)
    }
}

/* helper modified by LLM (iteration 5): relate spec string_to_int to seq_prefix_to_int for digit prefixes */
proof fn string_to_int_matches_seq_prefix(s: Seq<char>, pos: nat)
    requires
        1 <= pos,
        pos <= s.len(),
        forall|i: int| 0 <= i < pos ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9',
    ensures
        string_to_int(s.subrange(0, pos as int)) == seq_prefix_to_int(s, pos),
    decreases pos
{
    if pos == 1 {
        // single digit
        assert(string_to_int(s.subrange(0, 1 as int)) == string_to_int_helper(s.subrange(0, 1 as int), 0, 0));
        // string_to_int_helper will parse the single digit
        assert(string_to_int_helper(s.subrange(0, 1 as int), 0, 0) == (s[0 as int] as int - '0' as int));
        assert(seq_prefix_to_int(s, 1) == (s[0 as int] as int - '0' as int));
    } else {
        // pos > 1
        // relate string_to_int(s[0..pos]) to string_to_int_helper by unfolding last step
        // We use induction on pos
        string_to_int_matches_seq_prefix(s, pos - 1);
        // After the induction, the helper unfolding matches the recursive definition of seq_prefix_to_int
    }
}

/* helper modified by LLM (iteration 5): connect runtime-found newline position with spec find_newline */
proof fn find_newline_from(s: Seq<char>, start: nat, pos: nat)
    requires
        start <= s.len(),
        start <= pos <= s.len(),
        forall|i: int| start <= i < pos ==> s[i] != '\n',
        pos == s.len() || s[pos as int] == '\n',
    ensures
        find_newline(s, start) == pos,
    decreases pos - start
{
    if start >= s.len() {
        assert(find_newline(s, start) == s.len());
    } else if s[start as int] == '\n' {
        // then pos must be start
        assert(start == pos);
        assert(find_newline(s, start) == start);
    } else {
        // s[start] != '\n', so find_newline(s, start) == find_newline(s, start + 1)
        assert(s[start as int] != '\n');
        find_newline_from(s, start + 1, pos);
        assert(find_newline(s, start + 1) == pos);
        assert(find_newline(s, start) == find_newline(s, start + 1));
    }
}

// </vc-code>


}

fn main() {}