// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_fraction(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == '/') &&
    (forall|j: int| 0 <= j < s.len() ==> (s[j] == '/' || ('0' <= s[j] <= '9'))) &&
    (exists|k: int| 0 <= k < s.len() && #[trigger] s[k] == '/' && 
        k > 0 && k + 1 < s.len() &&
        string_to_int(s.subrange(0, k)) > 0 && string_to_int(s.subrange(k+1, s.len() as int)) > 0) &&
    (forall|i: int| 0 <= i < s.len() && #[trigger] s[i] == '/' ==> 
        i > 0 && i + 1 < s.len() &&
        string_to_int(s.subrange(0, i)) > 0 && string_to_int(s.subrange(i+1, s.len() as int)) > 0)
}

spec fn get_numerator(s: Seq<char>) -> int
    recommends valid_fraction(s)
{
    let slash_pos = find_slash(s);
    string_to_int(s.subrange(0, slash_pos))
}

spec fn get_denominator(s: Seq<char>) -> int
    recommends valid_fraction(s)
{
    let slash_pos = find_slash(s);
    string_to_int(s.subrange(slash_pos+1, s.len() as int))
}

spec fn find_slash(s: Seq<char>) -> int
    recommends exists|i: int| 0 <= i < s.len() && s[i] == '/'
{
    find_slash_helper(s, 0)
}

spec fn string_to_int(s: Seq<char>) -> int {
    string_to_int_helper(s, 0)
}

spec fn char_to_int(c: char) -> int {
    if c == '0' { 0 }
    else if c == '1' { 1 }
    else if c == '2' { 2 }
    else if c == '3' { 3 }
    else if c == '4' { 4 }
    else if c == '5' { 5 }
    else if c == '6' { 6 }
    else if c == '7' { 7 }
    else if c == '8' { 8 }
    else if c == '9' { 9 }
    else { 0 }
}

spec fn find_slash_helper(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos when 0 <= pos <= s.len() && exists|i: int| pos <= i < s.len() && s[i] == '/'
{
    if pos < s.len() && s[pos] == '/' { pos }
    else { find_slash_helper(s, pos + 1) }
}

spec fn string_to_int_helper(s: Seq<char>, acc: int) -> int
    decreases s.len()
{
    if s.len() == 0 { acc }
    else { string_to_int_helper(s.subrange(1, s.len() as int), acc * 10 + char_to_int(s[0])) }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use usize indexing to avoid nat/int casts in runtime code */
fn vec_find_slash(v: &Vec<char>) -> (pos: usize)
    requires
        v.len() > 0,
        exists|i: int| 0 <= i < v@.len() && v@[i] == '/',
    ensures
        0 <= pos as int && pos as int < v@.len(),
        v@[pos as int] == '/',
        forall|k: int| 0 <= k < pos as int ==> v@[k] != '/',
        pos as int == find_slash(v@),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i as int && i as int <= v@.len(),
            forall|k: int| 0 <= k < i as int ==> v@[k] != '/',
        decreases v.len() - i
    {
        if v[i] == '/' { break; }
        i += 1;
    }
    pos = i;
}

/* helper modified by LLM (iteration 2): compute integer value over a range using usize bounds */
fn vec_string_to_int_range(v: &Vec<char>, start: usize, end: usize) -> (res: int)
    requires
        start <= end && end <= v.len(),
    ensures
        res == string_to_int(v@.subrange(start as int, end as int)),
{
    let mut i: usize = start;
    let mut acc: int = 0;
    while i < end
        invariant
            start as int <= i as int && i as int <= end as int,
            acc == string_to_int(v@.subrange(start as int, i as int)),
        decreases end - i
    {
        let c: char = v[i];
        let digit: int = if c == '0' { 0 }
            else if c == '1' { 1 }
            else if c == '2' { 2 }
            else if c == '3' { 3 }
            else if c == '4' { 4 }
            else if c == '5' { 5 }
            else if c == '6' { 6 }
            else if c == '7' { 7 }
            else if c == '8' { 8 }
            else if c == '9' { 9 }
            else { 0 };
        acc = acc * 10 + digit;
        i += 1;
    }
    res = acc;
}
// </vc-helpers>

// <vc-spec>
fn simplify(x: Vec<char>, n: Vec<char>) -> (result: bool)
    requires 
        x.len() > 0 && n.len() > 0,
        exists|i: int| 0 <= i < x@.len() && x@[i] == '/',
        exists|j: int| 0 <= j < n@.len() && n@[j] == '/',
        forall|i: int| 0 <= i < x@.len() ==> (x@[i] == '/' || ('0' <= x@[i] <= '9')),
        forall|j: int| 0 <= j < n@.len() ==> (n@[j] == '/' || ('0' <= n@[j] <= '9')),
        valid_fraction(x@),
        valid_fraction(n@),
    ensures result <==> (get_numerator(x@) * get_numerator(n@)) % (get_denominator(x@) * get_denominator(n@)) == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute numerators/denominators using usize-indexed helpers */
    let pos_x = vec_find_slash(&x);
    let num_x = vec_string_to_int_range(&x, 0usize, pos_x);
    let den_x = vec_string_to_int_range(&x, pos_x + 1usize, x.len());
    let pos_n = vec_find_slash(&n);
    let num_n = vec_string_to_int_range(&n, 0usize, pos_n);
    let den_n = vec_string_to_int_range(&n, pos_n + 1usize, n.len());
    let prod_num = num_x * num_n;
    let prod_den = den_x * den_n;
    prod_num % prod_den == 0
}
// </vc-code>


}

fn main() {}