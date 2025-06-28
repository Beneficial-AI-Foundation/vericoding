use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires 0 < pre.len() <= str.len()
{
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> str@.index(j) == pre@.index(j)
    {
        if str@.index(i as int) != pre@.index(i as int) {
            return false;
        }
        i = i + 1;
    }
    true
}

// This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2
fn maxCommonSubstringLength(str1: String, str2: String) -> (len: nat)
    requires 0 < str1.len() && 0 < str2.len()
{
    let mut max_len: usize = 0;
    let mut i: usize = 0;
    
    while i < str1.len()
        invariant 
            0 <= i <= str1.len(),
            0 <= max_len
    {
        let mut j: usize = 0;
        while j < str2.len()
            invariant 
                0 <= j <= str2.len(),
                0 <= i < str1.len(),
                0 <= max_len
        {
            if str1@.index(i as int) == str2@.index(j as int) {
                // Found a match, now find the length of this common substring
                let mut k: usize = 0;
                while i + k < str1.len() && j + k < str2.len() && 
                      str1@.index((i + k) as int) == str2@.index((j + k) as int)
                    invariant
                        0 <= i < str1.len(),
                        0 <= j < str2.len(),
                        0 <= k,
                        i + k <= str1.len(),
                        j + k <= str2.len(),
                        0 <= max_len,
                        forall|l: int| 0 <= l < k ==> str1@.index((i as int) + l) == str2@.index((j as int) + l)
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
fn isSubstring(sub: String, str: String) -> (res: bool)
    requires 0 < sub.len() <= str.len()
{
    if sub.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str.len() - sub.len()
        invariant 
            0 <= i <= str.len() - sub.len() + 1,
            sub.len() <= str.len()
    {
        let mut j: usize = 0;
        let mut found = true;
        
        while j < sub.len()
            invariant 
                0 <= j <= sub.len(),
                0 <= i <= str.len() - sub.len(),
                i + j < str.len() || j == sub.len(),
                found == (forall|k: int| 0 <= k < j ==> str@.index((i as int) + k) == sub@.index(k))
        {
            if str@.index((i + j) as int) != sub@.index(j as int) {
                found = false;
                break;
            }
            j = j + 1;
        }
        
        if found && j == sub.len() {
            return true;
        }
        i = i + 1;
    }
    false
}

}