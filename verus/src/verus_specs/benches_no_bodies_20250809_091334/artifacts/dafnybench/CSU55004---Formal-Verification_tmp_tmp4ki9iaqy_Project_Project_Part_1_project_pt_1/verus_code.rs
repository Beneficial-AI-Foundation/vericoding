use vstd::prelude::*;

verus! {
    // Helper function to create a slice of a Vec<char>
    fn slice_vec(v: &Vec<char>, start: usize, end: usize) -> (result: Vec<char>)
        requires start <= end && end <= v.len(),
        ensures result.len() == end - start,
    {
    return Vec::new();  // TODO: Remove this line and implement the function body
    }

    // This method should return true iff pre is a prefix of str. That is, str starts with pre
    fn is_prefix(pre: &Vec<char>, str: &Vec<char>) -> (res: bool)
        requires 0 < pre.len() <= str.len(), // This line states that this method requires that pre is less than or equal in length to str
    {
    return false;  // TODO: Remove this line and implement the function body
    }

    // This method should return true iff sub is a substring of str. That is, str contains sub
    fn is_substring(sub: &Vec<char>, str: &Vec<char>) -> (res: bool)
        requires 0 < sub.len() <= str.len(), // This method requires that sub is less than or equal in length to str
    {
    return false;  // TODO: Remove this line and implement the function body
    }

    // This method should return true iff str1 and str2 have a common substring of length k
    fn have_common_k_substring(k: usize, str1: &Vec<char>, str2: &Vec<char>) -> (found: bool)
        requires 
            0 < k <= str1.len() && 0 < k <= str2.len(), // This method requires that k > 0 and k is less than or equal to in length to str1 and str2
    {
    return false;  // TODO: Remove this line and implement the function body
    }

    // This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2
    fn max_common_substring_length(str1: &Vec<char>, str2: &Vec<char>) -> (len: usize)
        requires 0 < str1.len() && 0 < str2.len(),
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Main to test each method
    fn main() {
    // TODO: Remove this comment and implement the function body
    }
}