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
/* helper modified by LLM (iteration 5): changed exec_string_to_int to use u64 to avoid ghost int in exec */
exec fn exec_find_slash(s: &Vec<char>) -> usize
    recommends exists|i: int| 0 <= i < s@.len() && s@[i] == '/'
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] != '/'
        decreases s.len() - i
    {
        if s[i] == '/' {
            return i;
        }
        i += 1;
    }
    0
}

exec fn exec_string_to_int(s: &Vec<char>) -> u64
    recommends forall|i: int| 0 <= i < s@.len() ==> '0' <= s@[i] <= '9'
{
    let mut result: u64 = 0;
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len()
        decreases s.len() - i
    {
        result = result * 10 + (s[i] as u64 - '0' as u64);
        i += 1;
    }
    result
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
/* code modified by LLM (iteration 5): fixed int usage by using u64 in exec */
{
    let x_slash_pos = exec_find_slash(&x);
    let x_num_slice = &x[0..x_slash_pos];
    let x_den_slice = &x[x_slash_pos+1..];
    let x_num = exec_string_to_int(x_num_slice);
    let x_den = exec_string_to_int(x_den_slice);

    let n_slash_pos = exec_find_slash(&n);
    let n_num_slice = &n[0..n_slash_pos];
    let n_den_slice = &n[n_slash_pos+1..];
    let n_num = exec_string_to_int(n_num_slice);
    let n_den = exec_string_to_int(n_den_slice);

    let product_num = x_num * n_num;
    let product_den = x_den * n_den;

    product_num % product_den == 0
}
// </vc-code>


}

fn main() {}