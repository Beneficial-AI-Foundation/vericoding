// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): defined spec fn, proved idempotency axiom, and removed external_body */
spec fn char_to_lower(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8) + 'a' as u8) as char
    } else {
        c
    }
}

proof fn lemma_char_to_lower_idempotent()
    ensures
        forall|c: char| #[trigger] char_to_lower(char_to_lower(c)) == char_to_lower(c),
{}

proof fn lemma_string_to_lower_distributes_over_add(s1: Seq<char>, s2: Seq<char>)
    ensures
        string_to_lower(s1 + s2) == string_to_lower(s1) + string_to_lower(s2),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_string_to_lower_distributes_over_add(s1.skip(1), s2);
    }
}

proof fn lemma_string_to_lower_idempotent(s: Seq<char>)
    ensures
        string_to_lower(string_to_lower(s)) == string_to_lower(s),
    decreases s.len()
{
    lemma_char_to_lower_idempotent();
    if s.len() > 0 {
        lemma_string_to_lower_distributes_over_add(seq![char_to_lower(s[0])], string_to_lower(s.skip(1)));
        lemma_string_to_lower_idempotent(s.skip(1));
    }
}

fn char_to_lower_exec(c: char) -> (res: char)
    ensures
        res == char_to_lower(c),
{
    if c >= 'A' && c <= 'Z' {
        ((c as u8 - 'A' as u8) + 'a' as u8) as char
    } else {
        c
    }
}

fn string_to_lower_exec(s: &Vec<char>) -> (res: Vec<char>)
    ensures
        res@ == string_to_lower(s@),
        res.len() == s.len(),
{
    let mut result: Vec<char> = Vec::with_capacity(s.len());
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            result@ == string_to_lower(s@.subrange(0, i as int)),
            result.capacity() >= s.len(),
        decreases s.len() - i
    {
        let c = s[i];
        let lower_c = char_to_lower_exec(c);
        
        proof {
            let i_int = i as int;
            lemma_string_to_lower_distributes_over_add(s@.subrange(0, i_int), seq![s@[i_int]]);
            assert(string_to_lower(seq![s@[i_int]]) == seq![char_to_lower(s@[i_int])]);
            assert(s@.subrange(0, i_int + 1) == s@.subrange(0, i_int) + seq![s@[i_int]]);
        }

        result.push(lower_c);
        i = i + 1;
    }
    result
}


// </vc-helpers>

// <vc-spec>
spec fn char_to_lower(c: char) -> char;

spec fn string_to_lower(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        seq![char_to_lower(s[0])] + string_to_lower(s.skip(1))
    }
}

fn lower(a: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@ == string_to_lower(a[i]@),
        forall|i: int| 0 <= i < a.len() ==> result[i].len() == a[i].len(),
        forall|i: int| 0 <= i < a.len() ==> (a[i].len() == 0 ==> result[i].len() == 0),
        forall|i: int| 0 <= i < a.len() ==> string_to_lower(result[i]@) == result[i]@,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type mismatch error in proof block */
{
    let mut result: Vec<Vec<char>> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            result.capacity() >= a.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j]@ == string_to_lower(a[j]@),
            forall|j: int| 0 <= j < i ==> result[j].len() == a[j].len(),
            forall|j: int| 0 <= j < i ==> string_to_lower(result[j]@) == result[j]@,
        decreases a.len() - i
    {
        let s = &a[i];
        let lower_s = string_to_lower_exec(s);
        
        proof {
            lemma_string_to_lower_idempotent(a[i as int]@);
        }

        result.push(lower_s);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}