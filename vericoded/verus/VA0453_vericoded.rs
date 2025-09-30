// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn determine_winner(n: int) -> &'static str
    recommends n >= 1
{
    if n == 1 { "FastestFinger" }
    else if n == 2 { "Ashishgup" }
    else if is_power_of_two(n) { "FastestFinger" }
    else if n % 4 != 2 { "Ashishgup" }
    else if is_limited_prime(n / 2) { "FastestFinger" }
    else { "Ashishgup" }
}

spec fn is_power_of_two(n: int) -> bool
    recommends n >= 1
    decreases n
{
    if n <= 0 { false }
    else { n == 1 || (n % 2 == 0 && is_power_of_two(n / 2)) }
}

spec fn is_limited_prime(p: int) -> bool
    recommends p >= 1
{
    if p <= 1 { false }
    else if p == 2 { true }
    else if p % 2 == 0 { false }
    else { true /* simplified primality check */ }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Implemented lemma body to prove winner validity. */
proof fn lemma_determine_winner_returns_valid_string(n: int)
    requires n >= 1
    ensures
        determine_winner(n) == "FastestFinger" || determine_winner(n) == "Ashishgup"
{
    if n == 1 {
        assert(determine_winner(n) == "FastestFinger");
    } else if n == 2 {
        assert(determine_winner(n) == "Ashishgup");
    } else if is_power_of_two(n) {
        assert(determine_winner(n) == "FastestFinger");
    } else if n % 4 != 2 {
        assert(determine_winner(n) == "Ashishgup");
    } else if is_limited_prime(n / 2) {
        assert(determine_winner(n) == "FastestFinger");
    } else {
        assert(determine_winner(n) == "Ashishgup");
    }
}

/* helper modified by LLM (iteration 3): No logical change, only updating comment. */
fn exec_is_power_of_two(n_in: i8) -> (res: bool)
    requires
        n_in >= 1,
    ensures
        res == is_power_of_two(n_in as int),
{
    let mut n = n_in;
    while n > 1
        invariant
            n >= 1,
            is_power_of_two(n_in as int) <==> is_power_of_two(n as int),
        decreases n
    {
        if n % 2 != 0 {
            return false;
        }
        n = n / 2;
    }
    true
}

/* helper modified by LLM (iteration 3): No logical change, only updating comment. */
fn exec_is_limited_prime(p: i8) -> (res: bool)
    requires
        p >= 1,
    ensures
        res == is_limited_prime(p as int),
{
    if p <= 1 {
        false
    } else if p == 2 {
        true
    } else if p % 2 == 0 {
        false
    } else {
        true
    }
}

/* helper modified by LLM (iteration 3): No logical change, only updating comment. */
fn exec_determine_winner(n_in: i8) -> (res: &'static str)
    requires
        n_in >= 1,
    ensures
        res == determine_winner(n_in as int),
{
    if n_in == 1 {
        "FastestFinger"
    } else if n_in == 2 {
        "Ashishgup"
    } else if exec_is_power_of_two(n_in) {
        "FastestFinger"
    } else if n_in % 4 != 2 {
        "Ashishgup"
    } else {
        if exec_is_limited_prime(n_in / 2) {
            "FastestFinger"
        } else {
            "Ashishgup"
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<&'static str>)
    requires
        input.len() >= 1,
        input[0] as int >= 1,
        input.len() == input[0] as int + 1,
        forall|i: int| #![auto] 1 <= i < input.len() ==> input[i as int] as int >= 1
    ensures
        result.len() == input[0] as int,
        forall|i: int| #![auto] 0 <= i < result.len() ==> result[i as int] == "FastestFinger" || result[i as int] == "Ashishgup",
        forall|i: int| #![auto] 1 <= i < input.len() ==> result[(i-1) as int] == determine_winner(input[i as int] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added invariant and lemma call to prove winner names are valid. */
    let mut result: Vec<&'static str> = Vec::new();
    let mut i: usize = 1;
    while i < input.len()
        invariant
            1 <= i && i <= input.len(),
            input.len() as int == input[0] as int + 1,
            result.len() == i - 1,
            forall|k: int| #![auto] 1 <= k < input.len() ==> input[k as int] as int >= 1,
            forall|j: int| #![auto] 1 <= j < i as int ==> 
                result@[(j - 1)] == determine_winner(input@[j] as int),
            forall|j: int| #![auto] 0 <= j < result.len() ==> 
                result@[j] == "FastestFinger" || result@[j] == "Ashishgup",
        decreases input.len() - i
    {
        let n = input[i];
        let winner = exec_determine_winner(n);
        proof {
            lemma_determine_winner_returns_valid_string(n as int);
        }
        result.push(winner);
        i = i + 1;
    }
    result
}

// </vc-code>


}

fn main() {}