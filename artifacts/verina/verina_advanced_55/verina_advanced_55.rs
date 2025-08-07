use vstd::prelude::*;
use std::collections::HashMap;

verus! {

// Precondition: list is non-empty
spec fn most_frequent_precond(xs: Seq<i32>) -> bool {
    xs.len() > 0
}

// Count occurrences of value x in sequence xs
spec fn count_occurrences(xs: Seq<i32>, x: i32) -> nat {
    xs.filter(|y: i32| y == x).len()
}

// Simple contains function for Vec
fn vec_contains(v: &Vec<i32>, x: i32) -> (result: bool) 
    ensures result <==> v@.contains(x)
{
    let mut i = 0;
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            !v@.subrange(0, i as int).contains(x)
        decreases v.len() - i
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

// Build a frequency map from the list  
fn count_map(xs: &Vec<i32>) -> (result: HashMap<i32, u32>)
    requires xs.len() > 0
{
    let mut map: HashMap<i32, u32> = HashMap::new();
    let mut i = 0;
    
    while i < xs.len()
        invariant 0 <= i <= xs.len()
        decreases xs.len() - i
    {
        let x = xs[i];
        let current = match map.get(&x) {
            Some(val) => *val,
            None => 0u32
        };
        map.insert(x, current + 1);
        i += 1;
    }
    
    map
}

// Compute the maximum frequency in the map
fn get_max_frequency(map: &HashMap<i32, u32>) -> (result: u32)
    requires map.len() > 0
{
    let mut max_freq = 0u32;
    
    for (k, v) in map.iter() {
        if *v > max_freq {
            max_freq = *v;
        }
    }
    
    max_freq
}

// Extract all keys whose frequency == max_freq
fn get_candidates(map: &HashMap<i32, u32>, max_freq: u32) -> (result: Vec<i32>)
{
    let mut candidates = Vec::new();
    
    for (k, v) in map.iter() {
        if *v == max_freq {
            candidates.push(*k);
        }
    }
    
    candidates
}

// Return the first candidate element from original list
fn get_first_with_freq(xs: &Vec<i32>, candidates: &Vec<i32>) -> (result: i32)
    requires 
        xs.len() > 0,
        candidates.len() > 0
{
    let mut i = 0;
    while i < xs.len()
        invariant 0 <= i <= xs.len()
        decreases xs.len() - i
    {
        if vec_contains(candidates, xs[i]) {
            return xs[i];
        }
        i += 1;
    }
    
    // fallback
    candidates[0]
}

// Main function
fn most_frequent(xs: Vec<i32>) -> (result: i32)
    requires most_frequent_precond(xs@)
    ensures most_frequent_postcond(xs@, result)
{
    let freq_map = count_map(&xs);
    let max_freq = get_max_frequency(&freq_map);
    let candidates = get_candidates(&freq_map, max_freq);
    
    // We need to assume candidates is non-empty
    // This corresponds to the "sorry" proof in the original Lean code
    proof {
        assume(candidates.len() > 0);
    }
    
    let first_result = get_first_with_freq(&xs, &candidates);
    
    proof {
        // Assume the postcondition holds (corresponds to "sorry" in original)
        assume(most_frequent_postcond(xs@, first_result));
    }
    
    first_result
}

// Postcondition specification
spec fn most_frequent_postcond(xs: Seq<i32>, result: i32) -> bool {
    // result is in xs
    xs.contains(result) &&
    // all elements have frequency <= frequency of result  
    (forall |x: i32| #![auto] xs.contains(x) ==> count_occurrences(xs, x) <= count_occurrences(xs, result)) &&
    // result is the first element with maximum frequency
    (forall |i: int| #![auto] 0 <= i < xs.len() && count_occurrences(xs, xs[i]) == count_occurrences(xs, result) ==> 
        exists |j: int| 0 <= j <= i && xs[j] == result)
}

} // verus!

fn main() {}