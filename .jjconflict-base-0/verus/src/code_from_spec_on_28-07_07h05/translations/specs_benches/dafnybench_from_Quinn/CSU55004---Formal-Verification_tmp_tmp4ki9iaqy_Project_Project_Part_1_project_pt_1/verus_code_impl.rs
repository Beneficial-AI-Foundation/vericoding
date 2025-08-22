use vstd::prelude::*;

verus! {
    /* code modified by LLM (iteration 4): Added decreases clause to while loop */
    // Helper function to compare two Vec<char> for equality
    fn vec_char_eq(v1: &Vec<char>, v2: &Vec<char>) -> (result: bool)
        ensures result == (v1.len() == v2.len() && forall|i: int| 0 <= i < v1.len() ==> v1[i] == v2[i]),
    {
        if v1.len() != v2.len() {
            return false;
        }
        
        let mut i = 0;
        while i < v1.len()
            invariant 
                0 <= i <= v1.len(),
                v1.len() == v2.len(),
                forall|j: int| 0 <= j < i ==> v1[j] == v2[j],
            decreases v1.len() - i,
        {
            if v1[i] != v2[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    /* code modified by LLM (iteration 4): Added bounds check for array access */
    // Helper function to create a slice of a Vec<char>
    fn slice_vec(v: &Vec<char>, start: usize, end: usize) -> (result: Vec<char>)
        requires start <= end && end <= v.len(),
        ensures result.len() == end - start,
    {
        let mut result = Vec::new();
        let mut i = start;
        while i < end
            invariant 
                start <= i <= end,
                result.len() == i - start,
                i <= v.len(),
            decreases end - i,
        {
            result.push(v[i]);
            i += 1;
        }
        result
    }

    /* code modified by LLM (iteration 4): Added bounds checks for array access */
    // This method should return true iff pre is a prefix of str. That is, str starts with pre
    fn is_prefix(pre: &Vec<char>, str: &Vec<char>) -> (res: bool)
        requires 0 < pre.len() <= str.len(), // This line states that this method requires that pre is less than or equal in length to str
    {
        let mut i = 0;
        while i < pre.len()
            invariant 
                0 <= i <= pre.len(),
                i <= str.len(),
                forall|j: int| 0 <= j < i ==> pre[j] == str[j],
            decreases pre.len() - i,
        {
            if pre[i] != str[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    /* code modified by LLM (iteration 4): Fixed bounds checks and arithmetic overflow issues */
    // This method should return true iff sub is a substring of str. That is, str contains sub
    fn is_substring(sub: &Vec<char>, str: &Vec<char>) -> (res: bool)
        requires 0 < sub.len() <= str.len(), // This method requires that sub is less than or equal in length to str
    {
        if sub.len() > str.len() {
            return false;
        }
        
        let mut i = 0;
        let max_i = str.len() - sub.len();
        while i <= max_i
            invariant 
                0 <= i <= max_i + 1,
                sub.len() <= str.len(),
                max_i == str.len() - sub.len(),
            decreases max_i + 1 - i,
        {
            let mut j = 0;
            let mut matches = true;
            while j < sub.len()
                invariant 
                    0 <= j <= sub.len(),
                    i <= max_i,
                    i + sub.len() <= str.len(),
                    matches == forall|k: int| 0 <= k < j ==> sub[k] == str[i + k],
                decreases sub.len() - j,
            {
                if sub[j] != str[i + j] {
                    matches = false;
                    break;
                }
                j += 1;
            }
            if matches {
                return true;
            }
            i += 1;
        }
        false
    }

    /* code modified by LLM (iteration 4): Fixed bounds checks and precondition issues */
    // This method should return true iff str1 and str2 have a common substring of length k
    fn have_common_k_substring(k: usize, str1: &Vec<char>, str2: &Vec<char>) -> (found: bool)
        requires 
            0 < k <= str1.len() && 0 < k <= str2.len(), // This method requires that k > 0 and k is less than or equal to in length to str1 and str2
    {
        if k > str1.len() || k > str2.len() {
            return false;
        }
        
        let mut i = 0;
        let max_i = str1.len() - k;
        while i <= max_i
            invariant 
                0 <= i <= max_i + 1,
                k <= str1.len(),
                max_i == str1.len() - k,
            decreases max_i + 1 - i,
        {
            let substr1 = slice_vec(str1, i, i + k);
            let mut j = 0;
            let max_j = str2.len() - k;
            while j <= max_j
                invariant 
                    0 <= j <= max_j + 1,
                    k <= str2.len(),
                    max_j == str2.len() - k,
                decreases max_j + 1 - j,
            {
                let substr2 = slice_vec(str2, j, j + k);
                /* code modified by LLM (iteration 2): Replaced direct equality with custom vec_char_eq function */
                if vec_char_eq(&substr1, &substr2) {
                    return true;
                }
                j += 1;
            }
            i += 1;
        }
        false
    }

    /* code modified by LLM (iteration 4): Fixed bounds checks and overflow issues */
    // This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2
    fn max_common_substring_length(str1: &Vec<char>, str2: &Vec<char>) -> (len: usize)
        requires 0 < str1.len() && 0 < str2.len(),
    {
        let mut max_len = 0;
        let mut k = 1;
        let max_possible = if str1.len() < str2.len() { str1.len() } else { str2.len() };
        
        while k <= max_possible
            invariant 
                1 <= k <= max_possible + 1,
                max_possible <= str1.len(),
                max_possible <= str2.len(),
            decreases max_possible + 1 - k,
        {
            if have_common_k_substring(k, str1, str2) {
                max_len = k;
            }
            k += 1;
        }
        max_len
    }

    /* code modified by LLM (iteration 2): Removed println! statements as they are not supported in Verus */
    // Main to test each method
    fn main() {
        let str1 = vec!['h', 'e', 'l', 'l', 'o'];
        let str2 = vec!['w', 'o', 'r', 'l', 'd'];
        let pre = vec!['h', 'e'];
        
        let is_pre = is_prefix(&pre, &str1);
        let max_len = max_common_substring_length(&str1, &str2);
        
        // Results computed but not printed since println! is not supported in Verus
    }
}