use vstd::prelude::*;

verus! {
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
        {
            result.push(v[i]);
            i += 1;
        }
        result
    }

    // This method should return true iff pre is a prefix of str. That is, str starts with pre
    fn is_prefix(pre: &Vec<char>, str: &Vec<char>) -> (res: bool)
        requires 0 < pre.len() <= str.len(), // This line states that this method requires that pre is less than or equal in length to str
    {
        let mut i = 0;
        while i < pre.len()
            invariant 
                0 <= i <= pre.len(),
                /* code modified by LLM (iteration 1): Fixed type mismatch by using sequence view @ for spec access */
                forall|j: int| 0 <= j < i ==> pre@[j] == str@[j],
        {
            if pre[i] != str[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    // This method should return true iff sub is a substring of str. That is, str contains sub
    fn is_substring(sub: &Vec<char>, str: &Vec<char>) -> (res: bool)
        requires 0 < sub.len() <= str.len(), // This method requires that sub is less than or equal in length to str
    {
        let mut start_pos = 0;
        
        while start_pos + sub.len() <= str.len()
            invariant 
                0 <= start_pos <= str.len() - sub.len() + 1,
        {
            let mut matches = true;
            let mut i = 0;
            
            while i < sub.len()
                invariant 
                    0 <= i <= sub.len(),
                    /* code modified by LLM (iteration 1): Fixed type mismatch by using sequence view @ for spec access */
                    matches ==> forall|j: int| 0 <= j < i ==> sub@[j] == str@[start_pos + j],
            {
                if sub[i] != str[start_pos + i] {
                    matches = false;
                    break;
                }
                i += 1;
            }
            
            if matches {
                return true;
            }
            
            start_pos += 1;
        }
        
        false
    }

    // This method should return true iff str1 and str2 have a common substring of length k
    fn have_common_k_substring(k: usize, str1: &Vec<char>, str2: &Vec<char>) -> (found: bool)
        requires 
            0 < k <= str1.len() && 0 < k <= str2.len(), // This method requires that k > 0 and k is less than or equal to in length to str1 and str2
    {
        let mut i = 0;
        
        while i + k <= str1.len()
            invariant 0 <= i <= str1.len() - k + 1,
        {
            let substr1 = slice_vec(str1, i, i + k);
            
            if is_substring(&substr1, str2) {
                return true;
            }
            
            i += 1;
        }
        
        false
    }

    // This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2
    fn max_common_substring_length(str1: &Vec<char>, str2: &Vec<char>) -> (len: usize)
        requires 0 < str1.len() && 0 < str2.len(),
    {
        let max_possible_len = if str1.len() <= str2.len() { str1.len() } else { str2.len() };
        let mut k = max_possible_len;
        
        while k > 0
            invariant 0 <= k <= max_possible_len,
        {
            if have_common_k_substring(k, str1, str2) {
                return k;
            }
            k -= 1;
        }
        
        0
    }

    // Main to test each method
    fn main() {
        let str1 = vec!['h', 'e', 'l', 'l', 'o'];
        let str2 = vec!['w', 'o', 'r', 'l', 'd'];
        let pre = vec!['h', 'e'];
        
        /* code modified by LLM (iteration 1): Removed println! statements as they are not supported in Verus */
        let is_pre = is_prefix(&pre, &str1);
        let has_sub = is_substring(&vec!['l', 'l'], &str1);
        let has_common = have_common_k_substring(1, &str1, &str2);
        let max_len = max_common_substring_length(&str1, &str2);
    }
}