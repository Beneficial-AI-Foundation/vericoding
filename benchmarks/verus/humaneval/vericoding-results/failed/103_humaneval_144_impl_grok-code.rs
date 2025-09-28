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
/* helper modified by LLM (iteration 5): added parentheses around ensures conditions and invariant clauses to fix compilation errors */fn exec_find_slash(v: Seq<char>) -> (idx: usize)
    requires exists|i: int| 0 <= i < v.len() && #[trigger] v[i] == '/',
    ensures
        (0 <= idx as int),
        (idx as int < v.len()),
        (v[idx] == '/'),
        (forall|j: int| 0 <= j < idx as int ==> v[j] != '/'),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            (0 <= i as int <= v.len()),
            (forall|j: int| 0 <= j < i as int ==> v[j] != '/'),
        decreases v.len() as int - i as int,
    {
        if v[i] == '/' {
            return i;
        }
        i = i + 1;
    }
    0
}

/* helper modified by LLM (iteration 5): avoided duplicate name and used usize for exec type */
fn exec_string_to_int(s: Seq<char>) -> (val: tracked<i64>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> ('0' <= s[i] <= '9'),
    ensures val@ == string_to_int(s),
{
    let tracked mut result: i64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            (0 <= i as int <= s.len()),
            (result@ == string_to_int(s.subrange(0, i as int))),
        decreases s.len() as int - i as int,
    {
        let digit: tracked<i64> = s[i] as u8 as i64 - '0' as u8 as i64;
        result = result@ * 10 + digit@;
        i = i + 1;
    }
    result
}

/* helper modified by LLM (iteration 5): avoided duplicate name, used tracked<i64> for unlimited int in exec */
fn exec_get_numerator(v: Vec<char>) -> (result: tracked<i64>)
    requires valid_fraction(v@),
    ensures result@ == get_numerator(v@),
{
    let slash_pos: int = exec_find_slash(v@) as int;
    exec_string_to_int(v@.subrange(0, slash_pos))
}

/* helper modified by LLM (iteration 5): avoided duplicate name, used tracked<i64> for unlimited int in exec */
fn exec_get_denominator(v: Vec<char>) -> (result: tracked<i64>)
    requires valid_fraction(v@),
    ensures result@ == get_denominator(v@),
{
    let slash_pos: int = exec_find_slash(v@) as int;
    exec_string_to_int(v@.subrange(slash_pos + 1, v@.len()))
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
    /* code modified by LLM (iteration 5): compute numerators and denominators using tracked types, then check if num1*num2 % den1*den2 ==0 */
    let num1 = exec_get_numerator(x)@;
    let den1 = exec_get_denominator(x)@;
    let num2 = exec_get_numerator(n)@;
    let den2 = exec_get_denominator(n)@;
    let product_num = num1 * num2;
    let product_den = den1 * den2;
    product_num % product_den == 0
}
// </vc-code>


}

fn main() {}