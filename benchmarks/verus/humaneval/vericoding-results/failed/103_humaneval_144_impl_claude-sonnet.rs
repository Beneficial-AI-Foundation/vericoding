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
/* helper modified by LLM (iteration 5): fixed return type to int for exec_string_to_int */
proof fn lemma_mod_zero_equiv(a: int, b: int)
    requires b > 0
    ensures (a % b == 0) <==> (exists|k: int| a == k * b)
{
}

proof fn lemma_fraction_properties(s: Seq<char>)
    requires valid_fraction(s)
    ensures get_numerator(s) > 0 && get_denominator(s) > 0
{
}

proof fn lemma_multiplication_mod(a: int, b: int, c: int, d: int)
    requires b > 0, d > 0, c * d > 0
    ensures ((a * c) % (b * d) == 0) <==> (exists|k: int| a * c == k * b * d)
{
    lemma_mod_zero_equiv(a * c, b * d);
}

exec fn exec_find_slash(chars: &Vec<char>) -> (pos: usize)
    requires chars@.len() > 0,
             exists|i: int| 0 <= i < chars@.len() && chars@[i] == '/'
    ensures 0 <= pos < chars@.len(),
            chars@[pos as int] == '/'
{
    let mut i = 0;
    while i < chars.len()
        invariant 0 <= i <= chars@.len(),
                  forall|j: int| 0 <= j < i ==> chars@[j] != '/'
    {
        if chars[i] == '/' {
            return i;
        }
        i += 1;
    }
    0
}

exec fn exec_string_to_int(chars: &Vec<char>, start: usize, end: usize) -> (result: int)
    requires 0 <= start <= end <= chars@.len(),
             forall|i: int| start <= i < end ==> ('0' <= chars@[i] <= '9')
    ensures result >= 0
{
    let mut acc: int = 0;
    let mut i = start;
    while i < end
        invariant start <= i <= end,
                  acc >= 0
    {
        let digit = match chars[i] {
            '0' => 0int,
            '1' => 1int,
            '2' => 2int,
            '3' => 3int,
            '4' => 4int,
            '5' => 5int,
            '6' => 6int,
            '7' => 7int,
            '8' => 8int,
            '9' => 9int,
            _ => 0int,
        };
        acc = acc * 10int + digit;
        i += 1;
    }
    acc
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
    /* code modified by LLM (iteration 5): fixed type coercion for int operations */
    lemma_fraction_properties(x@);
    lemma_fraction_properties(n@);
    
    let x_slash = exec_find_slash(&x);
    let n_slash = exec_find_slash(&n);
    
    let x_num = exec_string_to_int(&x, 0, x_slash);
    let x_den = exec_string_to_int(&x, x_slash + 1, x.len());
    let n_num = exec_string_to_int(&n, 0, n_slash);
    let n_den = exec_string_to_int(&n, n_slash + 1, n.len());
    
    proof {
        assert(x_num > 0 && x_den > 0 && n_num > 0 && n_den > 0);
        assert(x_den * n_den > 0);
        lemma_multiplication_mod(x_num, x_den, n_num, n_den);
    }
    
    let product_num = x_num * n_num;
    let product_den = x_den * n_den;
    
    (product_num % product_den) == 0int
}
// </vc-code>


}

fn main() {}