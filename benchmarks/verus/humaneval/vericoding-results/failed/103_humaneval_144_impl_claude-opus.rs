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
    /* code modified by LLM (iteration 4): fixed trigger annotation for quantifier */
    let x_num = calculate_numerator(&x);
    let x_den = calculate_denominator(&x);
    let n_num = calculate_numerator(&n);
    let n_den = calculate_denominator(&n);
    
    let product_num = x_num * n_num;
    let product_den = x_den * n_den;
    
    if product_den == 0 {
        return false;
    }
    
    let result = product_num % product_den == 0;
    
    proof {
        assert(x_num == get_numerator(x@));
        assert(x_den == get_denominator(x@));
        assert(n_num == get_numerator(n@));
        assert(n_den == get_denominator(n@));
        assert(result <==> (get_numerator(x@) * get_numerator(n@)) % (get_denominator(x@) * get_denominator(n@)) == 0);
    }
    
    result
}

fn calculate_numerator(s: &Vec<char>) -> (result: usize)
    requires
        s.len() > 0,
        valid_fraction(s@),
    ensures
        result == get_numerator(s@),
{
    let slash_pos = find_slash_exec(s);
    parse_int(s, 0, slash_pos)
}

fn calculate_denominator(s: &Vec<char>) -> (result: usize)
    requires
        s.len() > 0,
        valid_fraction(s@),
    ensures
        result == get_denominator(s@),
{
    let slash_pos = find_slash_exec(s);
    parse_int(s, slash_pos + 1, s.len())
}

fn find_slash_exec(s: &Vec<char>) -> (result: usize)
    requires
        s.len() > 0,
        exists|i: int| 0 <= i < s@.len() && s@[i] == '/',
    ensures
        0 <= result < s.len(),
        s@[result as int] == '/',
        result == find_slash(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] != '/',
            exists|k: int| i <= k < s@.len() && s@[k] == '/',
        decreases s.len() - i
    {
        if s[i] == '/' {
            proof {
                assert(s@[i as int] == '/');
                assert(i == find_slash(s@));
            }
            return i;
        }
        i = i + 1;
    }
    unreached()
}

fn parse_int(s: &Vec<char>, start: usize, end: usize) -> (result: usize)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| start <= i < end ==> #[trigger] ('0' <= s@[i] <= '9'),
    ensures
        result == string_to_int(s@.subrange(start as int, end as int)),
{
    let mut acc: usize = 0;
    let mut i: usize = start;
    
    while i < end
        invariant
            start <= i <= end,
            acc == string_to_int(s@.subrange(start as int, i as int)),
        decreases end - i
    {
        let digit = char_to_digit(s[i]);
        acc = acc * 10 + digit;
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(start as int, end as int) == s@.subrange(start as int, i as int));
    }
    
    acc
}

fn char_to_digit(c: char) -> (result: usize)
    requires '0' <= c <= '9',
    ensures result == char_to_int(c),
{
    if c == '0' { 0 }
    else if c == '1' { 1 }
    else if c == '2' { 2 }
    else if c == '3' { 3 }
    else if c == '4' { 4 }
    else if c == '5' { 5 }
    else if c == '6' { 6 }
    else if c == '7' { 7 }
    else if c == '8' { 8 }
    else { 9 }
}
// </vc-code>


}

fn main() {}