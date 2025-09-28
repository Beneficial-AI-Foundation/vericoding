// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_to_binary(n: nat) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else { int_to_binary_helper(n) }
}

spec fn int_to_binary_helper(n: nat) -> Seq<char>
    decreases n
{
    if n <= 1 { seq!['1'] }
    else { int_to_binary_helper(n / 2) + (if n % 2 == 1 { seq!['1'] } else { seq!['0'] }) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable converter from int to binary string consistent with spec helper */
fn to_binary_int_helper(n: int) -> (res: String)
    requires
        n > 0int,
    ensures
        res@ == int_to_binary_helper(n as nat),
    decreases n
{
    if n <= 1int {
        let mut s = String::new();
        s.push('1');
        s
    } else {
        let mut s = to_binary_int_helper(n / 2int);
        if n % 2int == 1int {
            s.push('1');
        } else {
            s.push('0');
        }
        s
    }
}

/* helper modified by LLM (iteration 5): executable wrapper handling zero case to match full spec */
fn to_binary_int(n: int) -> (res: String)
    requires
        n >= 0int,
    ensures
        res@ == int_to_binary(n as nat),
{
    if n == 0int {
        let mut s = String::new();
        s.push('0');
        s
    } else {
        to_binary_int_helper(n)
    }
}

/* helper modified by LLM (iteration 5): lemma that int_to_binary result has length >= 1 */
proof fn lemma_int_to_binary_len_ge_1(n: nat)
    ensures
        int_to_binary(n).len() >= 1,
    decreases n
{
    if n == 0 {
        assert(int_to_binary(0) == seq!['0']);
    } else {
        if n <= 1 {
            assert(int_to_binary(n) == int_to_binary_helper(n));
            assert(int_to_binary_helper(n) == seq!['1']);
        } else {
            assert(int_to_binary(n) == int_to_binary_helper(n));
            let tail = if n % 2 == 1 { seq!['1'] } else { seq!['0'] };
            assert(tail.len() == 1);
            assert(int_to_binary_helper(n) == int_to_binary_helper(n / 2) + tail);
            assert(int_to_binary_helper(n).len() == int_to_binary_helper(n / 2).len() + tail.len());
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn rounded_avg(n: int, m: int) -> (result: String)
    requires n > 0 && m > 0
    ensures (n > m) ==> (result@ == seq!['-', '1']) &&
            (n <= m) ==> (
        result@.len() >= 3 &&
        result@.subrange(0, 2) == seq!['0', 'b'] &&
        ({
            let count = m - n + 1;
            let total_sum = count * (n + m) / 2;
            let quotient = total_sum / count;
            let remainder = total_sum % count;
            let rounded = if remainder * 2 < count { quotient }
                         else if remainder * 2 > count { quotient + 1 }
                         else if quotient % 2 == 0 { quotient }
                         else { quotient + 1 };
            result@ == seq!['0', 'b'] + int_to_binary(rounded as nat)
        })
    )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix int literal suffixes and ensure positivity proofs */
    if n > m {
        return "-1".to_string();
    }

    assert(n <= m);

    let count = m - n + 1int;
    assert(count > 0int);

    let total_sum = count * (n + m) / 2int;
    assert(total_sum >= 0int);

    let quotient = total_sum / count;
    let remainder = total_sum % count;

    let rounded = if remainder * 2int < count {
        quotient
    } else if remainder * 2int > count {
        quotient + 1int
    } else if quotient % 2int == 0int {
        quotient
    } else {
        quotient + 1int
    };

    assert(quotient >= 0int);
    assert(remainder >= 0int);
    assert(rounded >= 0int);

    let t = to_binary_int(rounded);

    let mut s = String::new();
    s.push('0');
    s.push('b');
    s.push_str(&t);

    proof { lemma_int_to_binary_len_ge_1(rounded as nat); }

    s
}
// </vc-code>


}

fn main() {}