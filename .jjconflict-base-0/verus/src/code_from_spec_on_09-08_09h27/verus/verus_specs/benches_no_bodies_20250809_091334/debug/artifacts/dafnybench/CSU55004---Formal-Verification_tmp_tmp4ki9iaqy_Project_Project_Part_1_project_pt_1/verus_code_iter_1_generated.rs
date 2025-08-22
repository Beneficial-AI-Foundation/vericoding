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
                i <= pre.len(),
                forall|j: int| 0 <= j < i ==> pre[j as usize] == str[j as usize],
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
        let mut start = 0;
        while start <= str.len() - sub.len()
            invariant start <= str.len() - sub.len() + 1,
        {
            let mut matches = true;
            let mut i = 0;
            while i < sub.len()
                invariant 
                    i <= sub.len(),
                    matches == (forall|j: int| 0 <= j < i ==> sub[j as usize] == str[(start + j as usize) as usize]),
            {
                if sub[i] != str[start + i] {
                    matches = false;
                    break;
                }
                i += 1;
            }
            if matches {
                return true;
            }
            start += 1;
        }
        false
    }

    // This method should return true iff str1 and str2 have a common substring of length k
    fn have_common_k_substring(k: usize, str1: &Vec<char>, str2: &Vec<char>) -> (found: bool)
        requires 
            0 < k <= str1.len() && 0 < k <= str2.len(), // This method requires that k > 0 and k is less than or equal to in length to str1 and str2
    {
        let mut i = 0;
        while i <= str1.len() - k
            invariant i <= str1.len() - k + 1,
        {
            let sub1 = slice_vec(str1, i, i + k);
            let mut j = 0;
            while j <= str2.len() - k
                invariant j <= str2.len() - k + 1,
            {
                let sub2 = slice_vec(str2, j, j + k);
                if sub1.len() == sub2.len() {
                    let mut matches = true;
                    let mut idx = 0;
                    while idx < k
                        invariant 
                            idx <= k,
                            matches == (forall|m: int| 0 <= m < idx ==> sub1[m as usize] == sub2[m as usize]),
                    {
                        if sub1[idx] != sub2[idx] {
                            matches = false;
                            break;
                        }
                        idx += 1;
                    }
                    if matches {
                        return true;
                    }
                }
                j += 1;
            }
            i += 1;
        }
        false
    }

    // This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2
    fn max_common_substring_length(str1: &Vec<char>, str2: &Vec<char>) -> (len: usize)
        requires 0 < str1.len() && 0 < str2.len(),
    {
        let max_possible = if str1.len() < str2.len() { str1.len() } else { str2.len() };
        let mut k = max_possible;
        
        while k > 0
            invariant k <= max_possible,
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
        let prefix = vec!['h', 'e'];
        
        let is_pref = is_prefix(&prefix, &str1);
        let is_sub = is_substring(&vec!['l', 'l'], &str1);
        let has_common = have_common_k_substring(1, &str1, &str2);
        let max_len = max_common_substring_length(&str1, &str2);
        
        println!("Prefix test: {}", is_pref);
        println!("Substring test: {}", is_sub);
        println!("Common substring test: {}", has_common);
        println!("Max common length: {}", max_len);
    }
}