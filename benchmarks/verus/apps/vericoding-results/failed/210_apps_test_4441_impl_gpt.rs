// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0
}

spec fn expected_output(stdin_input: Seq<char>) -> Seq<char> {
    let lines = split_lines_func(stdin_input);
    if lines.len() >= 1 {
        let n = string_to_int(lines[0]);
        if n == 1 {
            seq!['H', 'e', 'l', 'l', 'o', ' ', 'W', 'o', 'r', 'l', 'd', '\n']
        } else if n != 1 && lines.len() >= 3 {
            let a = string_to_int(lines[1]);
            let b = string_to_int(lines[2]);
            int_to_string(a + b) + seq!['\n']
        } else {
            seq![]
        }
    } else {
        seq![]
    }
}

spec fn split_lines_func(s: Seq<char>) -> Seq<Seq<char>> {
    split_lines_func_helper(s, 0, seq![], seq![])
}

spec fn split_lines_func_helper(s: Seq<char>, i: int, current: Seq<char>, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases s.len() - i when 0 <= i <= s.len()
{
    if i >= s.len() {
        if current.len() == 0 { acc } else { acc.push(current) }
    } else if s[i] == '\n' {
        split_lines_func_helper(s, i + 1, seq![], acc.push(current))
    } else {
        split_lines_func_helper(s, i + 1, current.push(s[i]), acc)
    }
}

spec fn string_to_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s[0] == '-' {
        -string_to_int_helper(s.subrange(1, s.len() as int))
    } else {
        string_to_int_helper(s)
    }
}

spec fn string_to_int_helper(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        string_to_int_helper(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int)
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'] + int_to_string_helper(-n)
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    decreases n when n >= 0
{
    if n <= 0 {
        seq![]
    } else {
        int_to_string_helper(n / 10) + seq![(n % 10 + '0' as int) as char]
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn vecs_to_seqseq(vs: Seq<Vec<char>>) -> Seq<Seq<char>>
    decreases vs.len()
{
    if vs.len() == 0 {
        seq![]
    } else {
        vecs_to_seqseq(vs.subrange(0, vs.len() - 1)).push(vs[vs.len() - 1]@)
    }
}

proof fn lemma_vecs_to_seqseq_push(vs: Seq<Vec<char>>, v: Vec<char>)
    ensures vecs_to_seqseq(vs.push(v)) == vecs_to_seqseq(vs).push(v@)
{
    assert(vecs_to_seqseq(vs.push(v)) == vecs_to_seqseq(vs.push(v).subrange(0, vs.push(v).len() - 1)).push(vs.push(v)[vs.push(v).len() - 1]@));
    assert(vs.push(v).subrange(0, vs.push(v).len() - 1) == vs);
    assert(vs.push(v)[vs.push(v).len() - 1] == v);
}

proof fn lemma_string_to_int_helper_push(s: Seq<char>, c: char)
    ensures string_to_int_helper(s.push(c)) == string_to_int_helper(s) * 10 + (c as int - '0' as int)
{
    assert(string_to_int_helper(s.push(c)) == string_to_int_helper((s.push(c)).subrange(0, s.push(c).len() - 1)) * 10 + ((s.push(c))[s.push(c).len() - 1] as int - '0' as int));
    assert((s.push(c)).subrange(0, s.push(c).len() - 1) == s);
    assert((s.push(c))[s.push(c).len() - 1] == c);
}

fn string_to_int_helper_from_index(s: &Vec<char>, start: int) -> (res: int)
    requires
        0 <= start <= s.len() as int,
    ensures
        res == string_to_int_helper(s@.subrange(start, s.len() as int)),
{
    let mut i: int = start;
    let mut acc: int = 0;
    while i < s.len() as int
        invariant
            start <= i <= s.len() as int,
            acc == string_to_int_helper(s@.subrange(start, i)),
        decreases (s.len() as int) - i
    {
        let ch = s[i as usize];
        proof { lemma_string_to_int_helper_push(s@.subrange(start, i), ch); }
        acc = acc * 10 + (ch as int - '0' as int);
        i = i + 1;
    }
    acc
}

fn string_to_int_exec(s: &Vec<char>) -> (res: int)
    ensures
        res == string_to_int(s@),
{
    if s.len() == 0 {
        0
    } else {
        if s[0] == '-' {
            -string_to_int_helper_from_index(s, 1)
        } else {
            string_to_int_helper_from_index(s, 0)
        }
    }
}

fn int_to_string_helper_exec(n: int) -> (out: Vec<char>)
    requires
        n >= 0,
    ensures
        out@ == int_to_string_helper(n),
    decreases n
{
    if n <= 0 {
        Vec::new()
    } else {
        let mut v = int_to_string_helper_exec(n / 10);
        v.push(((n % 10 + '0' as int) as char));
        v
    }
}

fn int_to_string_exec(n: int) -> (out: Vec<char>)
    ensures
        out@ == int_to_string(n),
{
    if n == 0 {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        v
    } else if n < 0 {
        let mut res: Vec<char> = Vec::new();
        res.push('-');
        let t = int_to_string_helper_exec(-n);
        let mut i: int = 0;
        while i < t.len() as int
            invariant
                0 <= i <= t.len() as int,
                res@ == seq!['-'] + t@.subrange(0, i),
            decreases (t.len() as int) - i
        {
            let ch = t[i as usize];
            res.push(ch);
            i = i + 1;
        }
        res
    } else {
        int_to_string_helper_exec(n)
    }
}

fn split_lines_exec(s: &Vec<char>) -> (lines: Vec<Vec<char>>)
    ensures
        vecs_to_seqseq(lines@) == split_lines_func(s@),
{
    let mut i: int = 0;
    let mut acc: Vec<Vec<char>> = Vec::new();
    let mut cur: Vec<char> = Vec::new();

    while i < s.len() as int
        invariant
            0 <= i <= s.len() as int,
            split_lines_func_helper(s@, i, cur@, vecs_to_seqseq(acc@)) == split_lines_func(s@),
        decreases (s.len() as int) - i
    {
        let ch = s[i as usize];
        if ch == '\n' {
            proof { lemma_vecs_to_seqseq_push(acc@, cur); }
            let tmp = cur;
            acc.push(tmp);
            cur = Vec::new();
        } else {
            cur.push(ch);
        }
        i = i + 1;
    }

    if cur.len() == 0 {
        acc
    } else {
        proof { lemma_vecs_to_seqseq_push(acc@, cur); }
        let tmp2 = cur;
        acc.push(tmp2);
        acc
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures result@ == expected_output(stdin_input@)
// </vc-spec>
// <vc-code>
{
    let lines = split_lines_exec(&stdin_input);
    let mut out: Vec<char> = Vec::new();

    if lines.len() >= 1 {
        let n0 = string_to_int_exec(&lines[0]);
        if n0 == 1 {
            out.push('H'); out.push('e'); out.push('l'); out.push('l'); out.push('o');
            out.push(' ');
            out.push('W'); out.push('o'); out.push('r'); out.push('l'); out.push('d');
            out.push('\n');
        } else if lines.len() >= 3 {
            let a = string_to_int_exec(&lines[1]);
            let b = string_to_int_exec(&lines[2]);
            out = int_to_string_exec(a + b);
            out.push('\n');
        } else {
            // leave out empty
        }
    } else {
        // leave out empty
    }

    out
}
// </vc-code>


}

fn main() {}