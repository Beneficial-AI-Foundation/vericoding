use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    requires 0 < pre.len() <= str.len()
    ensures res ==> (forall|i: int| 0 <= i < pre.len() ==> str[i] == pre[i])
    ensures !res ==> (exists|i: int| 0 <= i < pre.len() && str[i] != pre[i])
{
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> str[j] == pre[j]
    {
        if str[i as int] != pre[i as int] {
            return false;
        }
        i = i + 1;
    }
    true
}

// This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2
fn maxCommonSubstringLength(str1: Seq<char>, str2: Seq<char>) -> (len: nat)
    requires 0 < str1.len() && 0 < str2.len()
    ensures len <= str1.len() && len <= str2.len()
{
    let mut max_len: usize = 0;
    let mut i: usize = 0;
    
    while i < str1.len()
        invariant 
            0 <= i <= str1.len(),
            0 <= max_len <= str1.len(),
            max_len <= str2.len()
    {
        let mut j: usize = 0;
        while j < str2.len()
            invariant 
                0 <= j <= str2.len(),
                0 <= i < str1.len(),
                0 <= max_len <= str1.len(),
                max_len <= str2.len()
        {
            if str1[i as int] == str2[j as int] {
                // Found a match, now find the length of this common substring
                let mut k: usize = 0;
                while i + k < str1.len() && j + k < str2.len() && 
                      str1[(i + k) as int] == str2[(j + k) as int]
                    invariant
                        0 <= i < str1.len(),
                        0 <= j < str2.len(),
                        0 <= k,
                        i + k <= str1.len(),
                        j + k <= str2.len(),
                        0 <= max_len <= str1.len(),
                        max_len <= str2.len(),
                        forall|l: int| 0 <= l < k ==> str1[(i as int) + l] == str2[(j as int) + l]
                {
                    k = k + 1;
                }
                if k > max_len {
                    max_len = k;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    max_len as nat
}

// This method should return true iff sub is a substring of str
fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    requires 0 < sub.len() <= str.len()
    ensures res ==> (exists|start: int| 0 <= start <= str.len() - sub.len() && 
                     (forall|i: int| 0 <= i < sub.len() ==> str[start + i] == sub[i]))
    ensures !res ==> (forall|start: int| 0 <= start <= str.len() - sub.len() ==> 
                      (exists|k: int| 0 <= k < sub.len() && str[start + k] != sub[k]))
    decreases str.len()
{
    let mut i: usize = 0;
    while i <= str.len() - sub.len()
        invariant 
            0 <= i <= str.len() - sub.len() + 1,
            sub.len() <= str.len(),
            sub.len() > 0,
            forall|start: int| 0 <= start < i ==> 
                (exists|k: int| 0 <= k < sub.len() && str[start + k] != sub[k])
        decreases str.len() - sub.len() + 1 - i
    {
        // Check if substring matches at position i
        let mut all_match = true;
        let mut j: usize = 0;
        
        while j < sub.len()
            invariant 
                0 <= j <= sub.len(),
                0 <= i <= str.len() - sub.len(),
                i + sub.len() <= str.len(),
                all_match ==> (forall|k: int| 0 <= k < j ==> str[(i as int) + k] == sub[k]),
                !all_match ==> (exists|k: int| 0 <= k < j && str[(i as int) + k] != sub[k])
            decreases sub.len() - j
        {
            if str[(i + j) as int] != sub[j as int] {
                all_match = false;
                proof {
                    assert(str[(i as int) + (j as int)] != sub[j as int]);
                    assert(exists|k: int| 0 <= k < j + 1 && str[(i as int) + k] != sub[k]) by {
                        assert(0 <= j < j + 1 && str[(i as int) + (j as int)] != sub[j as int]);
                    }
                }
            } else {
                j = j + 1;
            }
        }
        
        if all_match {
            // We found a complete match
            proof {
                assert(j == sub.len());
                assert(forall|k: int| 0 <= k < sub.len() ==> str[(i as int) + k] == sub[k]);
                assert(0 <= i <= str.len() - sub.len());
            }
            return true;
        } else {
            // No match at position i, establish invariant for next iteration
            proof {
                assert(exists|k: int| 0 <= k < sub.len() && str[(i as int) + k] != sub[k]);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        // When we exit the loop, we've checked all possible starting positions
        assert(i == str.len() - sub.len() + 1);
        assert(forall|start: int| 0 <= start <= str.len() - sub.len() ==> 
               (exists|k: int| 0 <= k < sub.len() && str[start + k] != sub[k]));
    }
    
    false
}

}