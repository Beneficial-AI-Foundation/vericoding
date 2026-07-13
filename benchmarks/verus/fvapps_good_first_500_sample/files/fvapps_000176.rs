// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn naive_compression_length(s: Seq<char>) -> nat
{
    s.len()
}

spec fn get_length_of_optimal_compression_spec(s: Seq<char>, k: nat) -> nat
{
    0
}

fn get_length_of_optimal_compression(s: Vec<char>, k: usize) -> (result: usize)
    requires 
        s.len() >= 1,
        k <= s.len(),
    ensures 
        result >= 0,
        result <= naive_compression_length(s@),
        result <= s.len(),
        result == get_length_of_optimal_compression_spec(s@, k as nat),
{
    // impl-start
    assume(false);
    0
    // impl-end
}

proof fn compressed_length_non_negative(s: Vec<char>, k: usize)
    requires s.len() >= 1, k <= s.len(),
    ensures get_length_of_optimal_compression_spec(s@, k as nat) >= 0,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn compressed_length_not_longer_than_naive(s: Vec<char>, k: usize)
    requires s.len() >= 1, k <= s.len(),
    ensures get_length_of_optimal_compression_spec(s@, k as nat) <= naive_compression_length(s@),
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn compressed_length_not_longer_than_original(s: Vec<char>, k: usize)
    requires s.len() >= 1, k <= s.len(),
    ensures get_length_of_optimal_compression_spec(s@, k as nat) <= s.len(),
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn binary_string_min_length(s: Vec<char>, k: usize)
    requires 
        s.len() > 0,
        k < s.len(),
    ensures get_length_of_optimal_compression_spec(s@, k as nat) >= 1,
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-spec>
// <vc-code>
// </vc-code>

/* Apps difficulty: interview */
/* Assurance level: unguarded */

/*
Test cases:
get_length_of_optimal_compression(vec!['a','a','a','b','c','c','c','d'], 2) should return 4
get_length_of_optimal_compression(vec!['a','a','b','b','a','a'], 2) should return 2
get_length_of_optimal_compression(vec!['a','a','a','a','a','a','a','a','a','a','a'], 0) should return 3
*/

}

fn main() {
    // let test1 = vec!['a','a','a','b','c','c','c','d'];
    // println!("{}", get_length_of_optimal_compression(test1, 2));
    // let test2 = vec!['a','a','b','b','a','a'];
    // println!("{}", get_length_of_optimal_compression(test2, 2));
    // let test3 = vec!['a','a','a','a','a','a','a','a','a','a','a'];
    // println!("{}", get_length_of_optimal_compression(test3, 0));
}