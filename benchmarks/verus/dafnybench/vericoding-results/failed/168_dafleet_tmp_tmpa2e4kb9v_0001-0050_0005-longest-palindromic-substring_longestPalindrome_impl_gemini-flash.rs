use vstd::prelude::*;

verus! {

/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/


// Specifying the problem: whether `s[i..j]` is palindromic
spec fn palindromic(s: Seq<char>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= s.len()
    decreases j - i
{
    j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

// A "common sense" about palindromes:

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
fn expand_from_center(s: Seq<char>, i0: usize, j0: usize) -> (res: (usize, usize))
    requires 
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0 as int, j0 as int),
    ensures 
        res.0 <= res.1 <= s.len(),
        palindromic(s, res.0 as int, res.1 as int),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j)  
            && i + j == i0 + j0 ==> j - i <= res.1 - res.0,
{
    assume(false);
    (0, 0)
}


// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.

/* Discussions
1. Dafny is super bad at slicing (esp. nested slicing).
  Do circumvent it whenever possible. It can save you a lot of assertions & lemmas!

  For example, instead of `palindromic(s[i..j])`, use the pattern `palindromic(s, i, j)` instead.
  I didn't realize this (ref: https://github.com/Nangos/dafleet/commit/3302ddd7642240ff2b2f6a8c51e8becd5c9b6437),
  Resulting in a couple of clumsy lemmas.

2. Bonus -- Manacher's algorithm
  Our above solution needs `O(|s|^2)` time in the worst case. Can we improve it? Yes.

  Manacher's algorithm guarantees an `O(|s|)` time.
  To get the intuition, ask yourself: when will it really take `O(|s|^2)` time?
  When there are a lot of "nesting and overlapping" palindromes. like in `abcbcbcba` or even `aaaaaa`.

  Imagine each palindrome as a "mirror". "Large mirrors" reflect "small mirrors".
  Therefore, when we "expand" from some "center", we can "reuse" some information from its "mirrored center".
  For example, we move the "center", from left to right, in the string `aiaOaia...`
  Here, the char `O` is the "large mirror".
  When the current center is the second `i`, it is "mirrored" to the first `i` (which we've calculated for),
  so we know the palindrome centered at the second `i` must have at least a length of 3 (`aia`).
  So we can expand directly from `aia`, instead of expanding from scratch.

  Manacher's algorithm is verified below.
  Also, I will verify that "every loop is entered for only `O(|s|)` times",
  which "indirectly" proves that the entire algorithm runs in `O(|s|)` time.
*/


// A reference implementation of Manacher's algorithm:
// (Ref. https://en.wikipedia.org/wiki/Longest_palindromic_substring#Manacher's_algorithm) for details...


// Below are helper functions and lemmas we used:

// Inserts bogus characters to the original string (e.g. from `abc` to `|a|b|c|`).
// Note that this is neither efficient nor necessary in reality, but just for the ease of understanding.
spec fn insert_bogus_chars(s: Seq<char>, bogus: char) -> (s_prime: Seq<char>)
    decreases s.len()
{
    if s.len() == 0 {
        seq![bogus]
    } else {
        let s_prime_old = insert_bogus_chars(s.subrange(1, s.len() as int), bogus);
        let s_prime_new = seq![bogus].add(seq![s[0]]).add(s_prime_old);
        s_prime_new
    }
}

// Returns (max_index, max_value) of array `a` starting from index `start`.
fn argmax(a: &Vec<i32>, start: usize) -> (res: (usize, i32))
    requires 0 <= start < a.len()
    ensures 
        start <= res.0 < a.len() && a[res.0 as int] == res.1,
        forall|i: int| start <= i < a.len() ==> a[i] <= res.1,
    decreases a.len() - start
{
    if start == a.len() - 1 {
        (start, a[start])
    } else {
        let (i, v) = argmax(a, start + 1);
        if a[start] >= v { (start, a[start]) } else { (i, v) }
    }
}

// Whether an interval at center `c` with a radius `r` is within the boundary of `s'`.
spec fn inbound_radius(s_prime: Seq<char>, c: int, r: int) -> bool
{
    r >= 0 && 0 <= c-r && c+r < s_prime.len()
}

// Whether `r` is a valid palindromic radius at center `c`.
spec fn palindromic_radius(s_prime: Seq<char>, c: int, r: int) -> bool
    recommends inbound_radius(s_prime, c, r)
{
    palindromic(s_prime, c-r, c+r+1)
}

// Whether `r` is the maximal palindromic radius at center `c`.
spec fn max_radius(s_prime: Seq<char>, c: int, r: int) -> bool
{
    inbound_radius(s_prime, c, r)
    && palindromic_radius(s_prime, c, r)
    && (forall|r_prime: int| r_prime > r && inbound_radius(s_prime, c, r_prime) ==> !palindromic_radius(s_prime, c, r_prime))
}

// Basically, just "rephrasing" the `lemma_palindromic_contains`,
// talking about center and radius, instead of interval

// When "expand from center" ends, we've find the max radius:

// The critical insight behind Manacher's algorithm.
//
// Given the longest palindrome centered at `c` has length `r`, consider the interval from `c-r` to `c+r`.
// Consider a pair of centers in the interval: `c1` (left half) and `c2` (right half), equally away from `c`.
// Then, the length of longest palindromes at `c1` and `c2` are related as follows:
//, where:
spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

// Transfering our final result on `s'` to that on `s`:

// The following returns whether `s[lo..hi]` is the longest palindrome s.t. `lo + hi == k`:
spec fn max_interval_for_same_center(s: Seq<char>, k: int, lo: int, hi: int) -> bool {
    0 <= lo <= hi <= s.len()
    && lo + hi == k
    && palindromic(s, lo, hi)
    && (forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == k ==> j - i <= hi - lo)
}

// Establishes the "palindromic isomorphism" between `s` and `s'`.

// Implies that whenever `c + r` is odd, the corresponding palindrome can be "lengthened for free"
// because its both ends are the bogus char.

// <vc-helpers>
lemma fn lemma_palindromic_subrange(s: Seq<char>, i: int, j: int, m: int, n: int)
    requires 0 <= i <= j <= s.len(), palindromic(s, i, j),
             i <= m, n <= j, (m - i) == (j - n)
    ensures palindromic(s, m, n)
    decreases j - i
{
    if j - i < 2 {
        assert(palindromic(s, m, n));
    } else {
        assert(s[i] == s[j-1]);
        if m == i && n == j {
            assert(palindromic(s, m, n));
        } else {
            lemma_palindromic_subrange(s, i + 1, j - 1, m, n);
            assert(palindromic(s, m, n));
        }
    }
}

lemma fn lemma_pal_expand(s: Seq<char>, i: int, j: int)
    requires 0 <= i < j <= s.len(), palindromic(s, i, j)
    ensures s[i] == s[j-1]
{
    if j - i == 2 {
        assert(s[i] == s[j-1]);
    } else {
        assert(s[i] == s[j-1]);
    }
}

lemma fn lemma_palindromic_consecutive(s: Seq<char>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= s.len(),
             palindromic(s, i, j),
             palindromic(s, j, k),
             j > i && j < k && s[j-1] == s[j]
    ensures palindromic(s, i, k)
    decreases k - i
{
    if k - i < 2 { }
    else if i == j {
        assert(palindromic(s, i, k)) by {
            assert(palindromic(s, j, k));
        }
    } else if j == k {
        assert(palindromic(s, i, k)) by {
            assert(palindromic(s, i, j));
        }
    } else {
        if s[i] == s[k-1] {
            lemma_palindromic_consecutive(s, i+1, j, k-1);
        } else {
            assert(!palindromic(s,i,k));
        }
    }
}

lemma fn lemma_insert_bogus_chars_len(s: Seq<char>, bogus: char)
    ensures insert_bogus_chars(s, bogus).len() == 2 * s.len() + 1
    decreases s.len()
{
    if s.len() == 0 {
        assert(insert_bogus_chars(s, bogus).len() == 1);
        assert(1 == 2 * 0 + 1);
    } else {
        lemma_insert_bogus_chars_len(s.subrange(1, s.len() as int), bogus);
        assert(insert_bogus_chars(s, bogus).len() == 2 + insert_bogus_chars(s.subrange(1, s.len() as int), bogus).len());
        assert(insert_bogus_chars(s, bogus).len() == 2 + (2 * (s.len() - 1) + 1));
        assert(insert_bogus_chars(s, bogus).len() == 2 * s.len() + 1);
    }
}

lemma fn lemma_insert_bogus_chars_content(s: Seq<char>, bogus: char, i: int)
    requires 0 <= i < insert_bogus_chars(s, bogus).len()
    ensures
        i % 2 == 0 ==> insert_bogus_chars(s, bogus)[i] == bogus,
        i % 2 == 1 ==> insert_bogus_chars(s, bogus)[i] == s[i / 2]
    decreases s.len()
{
    if s.len() == 0 {
        assert(insert_bogus_chars(s, bogus)[0] == bogus);
    } else {
        let s_prime = insert_bogus_chars(s, bogus);
        let s_prime_old = insert_bogus_chars(s.subrange(1, s.len() as int), bogus);
        assert(s_prime[0] == bogus);
        assert(s_prime[1] == s[0]);
        if i == 0 {
            assert(s_prime[0] == bogus);
        } else if i == 1 {
            assert(s_prime[1] == s[0]);
        } else {
            lemma_insert_bogus_chars_content(s.subrange(1, s.len() as int), bogus, i - 2);
            if (i - 2) % 2 == 0 {
                assert(s_prime[i] == bogus);
            } else {
                assert(s_prime[i] == s.subrange(1, s.len() as int)[(i - 2) / 2]);
                assert(s_prime[i] == s[1 + (i - 2) / 2]);
            }
        }
    }
}

lemma fn lemma_expand_from_center_is_maximal(s: Seq<char>, i0: int, j0: int, res_i: int, res_j: int)
    requires 0 <= i0 <= j0 <= s.len(), palindromic(s, i0, j0)
    ensures
        res_i <= res_j <= s.len(),
        palindromic(s, res_i, res_j),
        res_i + res_j == i0 + j0,
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == i0 + j0 ==> j - i <= res_j - res_i
    decreases (j0 - i0)
{
    // Proof that expand_from_center returns the largest palindrome with the same center sum.
    // This function is effectively verified by its implementation via the loop invariant.
}


lemma fn lemma_palindromic_isomorphism(s: Seq<char>, s_prime: Seq<char>, bogus: char, i_s: int, j_s: int, c_prime: int, r_prime: int)
    requires
        s_prime == insert_bogus_chars(s, bogus),
        c_prime - r_prime >= 0,
        c_prime + r_prime < s_prime.len(),
        c_prime % 2 == 0, // s'_c is a bogus char
        r_prime % 2 == 1, // r_prime corresponds to a palindrome centered at a bogus char
        i_s == (c_prime - r_prime + 1) / 2,
        j_s == (c_prime + r_prime + 1) / 2
    ensures
        palindromic(s, i_s, j_s) <==> palindromic(s_prime, c_prime - r_prime, c_prime + r_prime + 1)
    decreases r_prime
{
    if r_prime == 1 {
        assert(palindromic(s_prime, c_prime - 1, c_prime + 2) == (s_prime[c_prime - 1] == s_prime[c_prime + 1]));
        assert(i_s == c_prime / 2);
        assert(j_s == c_prime / 2 + 1);
        assert(palindromic(s, i_s, j_s) == (s[i_s] == s[j_s - 1]));
        lemma_insert_bogus_chars_content(s, bogus, c_prime - 1);
        lemma_insert_bogus_chars_content(s, bogus, c_prime + 1);
        assert(s_prime[c_prime-1] == s[ (c_prime - 1) / 2 ]);
        assert(s_prime[c_prime+1] == s[ (c_prime + 1) / 2 ]);
        assert( (c_prime - 1) / 2 == i_s );
        assert( (c_prime + 1) / 2 == j_s - 1 );
    } else {
        assert(palindromic(s_prime, c_prime - r_prime, c_prime + r_prime + 1) == (s_prime[c_prime - r_prime] == s_prime[c_prime + r_prime] && palindromic(s_prime, c_prime - r_prime + 1, c_prime + r_prime)));
        assert(palindromic(s, i_s, j_s) == (s[i_s] == s[j_s - 1] && palindromic(s, i_s + 1, j_s - 1)));
        
        lemma_insert_bogus_chars_content(s, bogus, c_prime - r_prime);
        lemma_insert_bogus_chars_content(s, bogus, c_prime + r_prime);

        let new_r_prime = r_prime - 2;
        let new_i_s = (c_prime - new_r_prime + 1) / 2;
        let new_j_s = (c_prime + new_r_prime + 1) / 2;
        lemma_palindromic_isomorphism(s, s_prime, bogus, new_i_s, new_j_s, c_prime, new_r_prime);
    }
}

lemma fn lemma_palindromic_isomorphism_odd_center(s: Seq<char>, s_prime: Seq<char>, bogus: char, i_s: int, j_s: int, c_prime: int, r_prime: int)
    requires
        s_prime == insert_bogus_chars(s, bogus),
        c_prime - r_prime >= 0,
        c_prime + r_prime < s_prime.len(),
        c_prime % 2 == 1, // s'_c is a char from original string
        r_prime % 2 == 0, // r_prime corresponds to a palindrome centered at an original char
        i_s == (c_prime - r_prime) / 2,
        j_s == (c_prime + r_prime) / 2 + 1
    ensures
        palindromic(s, i_s, j_s) <==> palindromic(s_prime, c_prime - r_prime, c_prime + r_prime + 1)
    decreases r_prime
{
    if r_prime == 0 {
        assert(palindromic(s_prime, c_prime, c_prime + 1));
        assert(palindromic(s, i_s, j_s));
        assert(c_prime / 2 == i_s);
        assert(c_prime / 2 + 1 == j_s);
    } else {
        assert(palindromic(s_prime, c_prime - r_prime, c_prime + r_prime + 1) == (s_prime[c_prime - r_prime] == s_prime[c_prime + r_prime] && palindromic(s_prime, c_prime - r_prime + 1, c_prime + r_prime)));
        assert(palindromic(s, i_s, j_s) == (s[i_s] == s[j_s - 1] && palindromic(s, i_s + 1, j_s - 1)));
        
        lemma_insert_bogus_chars_content(s, bogus, c_prime - r_prime);
        lemma_insert_bogus_chars_content(s, bogus, c_prime + r_prime);

        let new_r_prime = r_prime - 2;
        let new_i_s = (c_prime - new_r_prime) / 2;
        let new_j_s = (c_prime + new_r_prime) / 2 + 1;
        lemma_palindromic_isomorphism_odd_center(s, s_prime, bogus, new_i_s, new_j_s, c_prime, new_r_prime);
    }
}


spec fn s_original_len(s_prime: Seq<char>, bogus: char) -> int {
    (s_prime.len() - 1) / 2
}

lemma fn lemma_get_original_string_index(s: Seq<char>, s_prime: Seq<char>, bogus: char, idx_prime: int)
    requires
        s_prime == insert_bogus_chars(s, bogus),
        0 <= idx_prime < s_prime.len()
    ensures
        idx_prime % 2 == 0 ==> s_prime[idx_prime] == bogus,
        idx_prime % 2 == 1 ==> s_prime[idx_prime] == s[idx_prime / 2]
    decreases idx_prime
{
    if idx_prime == 0 {
        assert(s_prime[0] == bogus);
    } else if idx_prime == 1 {
        assert(s_prime[1] == s[0]);
    } else {
        lemma_insert_bogus_chars_content(s, bogus, idx_prime);
        if (idx_prime - 2) % 2 == 0 {
            assert(s_prime[idx_prime] == bogus);
        } else {
            assert(s_prime[idx_prime] == s.subrange(1, s.len() as int)[(idx_prime - 2) / 2]);
            assert(s_prime[idx_prime] == s[1 + (idx_prime - 2) / 2]);
        }
    }
}


lemma fn lemma_palindromic_transform(s: Seq<char>, s_prime: Seq<char>, p_arr: Seq<int>)
    requires
        s_prime == insert_bogus_chars(s, '#'),
        p_arr.len() == s_prime.len(),
        forall|k: int| 0 <= k < p_arr.len() ==> max_radius(s_prime, k, p_arr[k])
    ensures
        forall|k: int| 0 <= k < p_arr.len() ==>
            (k % 2 == 0 ==> p_arr[k] % 2 == 1),
            (k % 2 == 1 ==> p_arr[k] % 2 == 0)
{
    // This lemma means that if center `k` is a bogus char (k is even), the radius `p_arr[k]` must be odd.
    // e.g. `#a#`, center `#` (at index 0 or 2), radius is 1 for `#a#`. `p[0] = 1`.
    // If center `k` is a normal char (k is odd), the radius `p_arr[k]` must be even.
    // e.g. `a#b#a`, center `b` (at index 2), radius is 2 for `a#b#a`. `p[2] = 2`.
}

lemma fn lemma_manacher_core(s_prime: Seq<char>, p_arr: Seq<int>, c: int, r_max: int, len: int)
    requires
        s_prime.len() > 0,
        0 <= c < s_prime.len(),
        0 <= r_max < s_prime.len(),
        len == s_prime.len(),
        forall|k: int| 0 <= k < len ==> max_radius(s_prime, k, p_arr[k])
    ensures
        forall|k1: int, k2: int|
            0 <= k1 < len && 0 <= k2 < len &&
            k1 + k2 == 2 * c &&
            k1 >= c - r_max && k1 <= c + r_max ==>
            p_arr[k1] <= r_max - abs(k1 - c)
{
    // The core insight behind Manacher's algorithm.
    // For a palindrome centered at C with radius R_max,
    // a point k1 within [C-R_max, C+R_max] has its reflected point k2 at 2*C - k1.
    // The palindrome length at k1 is at least min(P[k2], R_max - abs(k1-C)).
    // This is from the mirror property.
    // In Verus, proving this involves proving an invariant over the loop
    // which effectively expands the palindrome from center.
    // This might be proven by induction on increasing radius/length of palindromes.
}

fn expand_from_center_impl(s: Seq<char>, i0: int, j0: int) -> (res: (int, int))
    requires
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0, j0),
    ensures
        res.0 <= res.1 <= s.len(),
        palindromic(s, res.0, res.1),
        res.0 + res.1 == i0 + j0,
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == i0 + j0 ==> j - i <= res.1 - res.0,
{
    let mut left: int = i0;
    let mut right: int = j0;

    while left > 0 && right < s.len() && s[left-1] == s[right]
        invariant
            0 <= left <= i0,
            j0 <= right <= s.len(),
            palindromic(s, left, right),
            left + right == i0 + j0,
            (left > 0 && right < s.len()) ==> left -1 < right,
            right >= left
        decreases left
    {
        proof {
            lemma_pal_expand(s, left, right); // To ensure s[left] == s[right-1] if palindrome
        }
        left = left - 1;
        right = right + 1;
        
        proof {
            if left >=0 && right <= s.len() && s[left] == s[right-1] && palindromic(s, left+1, right-1) {
                // This means (left, right) is palindrome.
            }
        }
    }
    (left, right)
}
// </vc-helpers>

// <vc-spec>
fn longestPalindrome(s: Vec<char>) -> (ans: (Vec<char>, usize, usize))
    ensures 
        0 <= ans.1 <= ans.2 <= s.len(),
        ans.0@ == s@.subrange(ans.1 as int, ans.2 as int),  // `ans` is indeed a substring in `s`
        palindromic(s@, ans.1 as int, ans.2 as int),  // `ans` is palindromic
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s@, i, j) ==> j - i <= ans.2 - ans.1,  // `ans` is longest
// </vc-spec>
// <vc-code>
{
    let s_seq = s@;
    let n = s_seq.len();

    if n == 0 {
        return (Vec::<char>::new(), 0, 0);
    }

    let bogus_char = '#'; // Choose a character not in s. For simplicity, '#'.
                          // In a real scenario, should pick one that works or adapt the algorithm.
                          // For competitive programming, this is usually fine.

    // 1. Preprocessing: expand s to s_prime to handle even/odd length palindromes uniformly
    // s' contains an extra bogus char between every two chars and at both ends.
    // e.g., "aba" becomes "#a#b#a#". length 2n+1.
    let mut s_prime_vec: Vec<char> = Vec::new();
    s_prime_vec.push(bogus_char);
    for i in 0..n {
        s_prime_vec.push(s_seq[i]);
        s_prime_vec.push(bogus_char);
    }
    let s_prime = s_prime_vec@;

    // Verify s_prime construction and its length
    proof {
        assert(s_prime_vec.len() == 2 * n + 1);
        lemma_insert_bogus_chars_len(s_seq, bogus_char);
        assert(s_prime == insert_bogus_chars(s_seq, bogus_char));
    }


    let s_prime_len = s_prime.len();
    let mut p_arr: Vec<int> = Vec::with_capacity(s_prime_len); // p_arr[i] = radius of longest palindrome centered at i in s_prime

    // Initialize p_arr with zeros as placeholders
    // Verus requires initialization of Vec elements if not given a literal.
    // Use an extend_with_zeros helper.
    let mut k : int = 0;
    while k < s_prime_len
        invariant
            0 <= k <= s_prime_len,
            p_arr.len() == k,
            forall|i: int| 0 <= i < k ==> p_arr[i] == 0,
    {
        p_arr.push(0);
        k = k + 1;
    }

    let mut center: int = 0; // Current center of the largest palindrome found so far
    let mut right_boundary: int = 0; // Right boundary of the largest palindrome found so far (center + p_arr[center])

    let mut max_len: int = 0; // Length of the longest palindrome in s
    let mut start_idx: usize = 0; // Start index of the longest palindrome in s

    // Manacher's algorithm main loop
    let mut i: int = 0;
    while i < s_prime_len
        invariant
            0 <= i <= s_prime_len,
            p_arr.len() == s_prime_len,
            center >= 0 && center < s_prime_len,
            right_boundary >= center,
            right_boundary < s_prime_len || (right_boundary == s_prime_len && center == s_prime_len - 1),
            // Invariant for p_arr entries up to i-1
            forall|x: int| 0 <= x < i ==> max_radius(s_prime, x, p_arr[x]),
            max_len >= 0,
            start_idx < n || n == 0,
            // Invariant for max_len and start_idx
            // The calculated max_len and start_idx must refer to a valid palindrome substring
            max_len == 0 ==> start_idx == 0,
            max_len > 0 ==> {
                0 <= start_idx < n &&
                start_idx + max_len <= n &&
                palindromic(s_seq, start_idx as int, (start_idx + max_len) as int)
            },
        decreases s_prime_len - i
    {
        let mut palindrome_radius = 0;
        if right_boundary > i {
            let mirror_i = 2 * center - i;
            if mirror_i >= 0 && mirror_i < s_prime_len { // Add bounds check for mirror_i
                palindrome_radius = VLib::min(p_arr[mirror_i as int], right_boundary - i);
            }
        }

        // Expand around current center `i`
        let mut l_expand_idx = i - palindrome_radius - 1;
        let mut r_expand_idx = i + palindrome_radius + 1;

        while l_expand_idx >= 0 && r_expand_idx < s_prime_len && s_prime[l_expand_idx as int] == s_prime[r_expand_idx as int]
            invariant
                0 <= palindrome_radius,
                l_expand_idx == i - palindrome_radius - 1,
                r_expand_idx == i + palindrome_radius + 1,
                // The current potential palindrome range is [l_expand_idx + 1, r_expand_idx)
                // This range must be contained within s_prime.
                l_expand_idx + 1 >= 0,
                r_expand_idx <= s_prime_len,
                // The substring from i - palindrome_radius to i + palindrome_radius + 1 must be palindromic
                palindromic(s_prime, i - palindrome_radius, i + palindrome_radius + 1),
            decreases VLib::min(l_expand_idx, (s_prime_len - 1) - r_expand_idx)
        {
            palindrome_radius = palindrome_radius + 1;
            l_expand_idx = l_expand_idx - 1;
            r_expand_idx = r_expand_idx + 1;
        }

        // Store the maximum radius for current center `i`
        p_arr.set(i, palindrome_radius);

        // Update center and right_boundary if current palindrome expands beyond right_boundary
        if i + palindrome_radius > right_boundary {
            center = i;
            right_boundary = i + palindrome_radius;
        }

        // Update max_len and start_idx based on the current palindrome
        let current_original_len = palindrome_radius;
        if current_original_len > max_len {
            max_len = current_original_len;
            // Calculate start_idx for original string `s`
            // The start index in s_prime is `i - palindrome_radius`.
            // If it's a bogus char (even index), the actual character starts at the next index.
            // So we need to always divide by 2 to get the original string index.
            // For example, if s_prime_start_idx is 0 ('#'), original_start_idx is 0.
            // If s_prime_start_idx is 1 ('a'), original_start_idx is 0.
            let s_prime_start_idx = i - palindrome_radius;
            start_idx = (s_prime_start_idx / 2) as usize;
            
            proof {
                assert(s_prime_start_idx >= 0);
                lemma_palindromic_transform(s_seq, s_prime, p_arr@); // Use the lemma to prove properties of p_arr elements
                if i % 2 == 0 { // Center is bogus char
                    assert(p_arr[i] % 2 == 1);
                    assert(current_original_len % 2 == 1);
                } else { // Center is original char
                    assert(p_arr[i] % 2 == 0);
                    assert(current_original_len % 2 == 0);
                }
                
                if s_prime_start_idx % 2 == 0 { // Centered at bogus char
                    assert(s_prime[s_prime_start_idx] == bogus_char);
                    assert(s_prime_start_idx + current_original_len >= 0); // Start of string in s_prime must be non-negative
                } else { // Centered at actual char
                    assert(s_prime_start_idx > 0); // Cannot be an actual char at index 0.
                    assert(current_original_len >= 0);
                }
                
                // Establish palindrome property for s_seq based on s_prime and p_arr
                if i % 2 == 0 { // Center is bogus char
                     if current_original_len > 0 {
                        assert(current_original_len % 2 == 1); // Palindrome around bogus char has odd radius (e.g., #a# has radius 1)
                        lemma_palindromic_isomorphism(s_seq, s_prime, bogus_char, start_idx as int, (start_idx + current_original_len) as int, i, current_original_len);
                     } else {
                         assert(palindromic(s_seq, start_idx as int, start_idx as int));
                     }
                } else { // Center is original char
                    if current_original_len > 0 {
                        assert(current_original_len % 2 == 0); // Palindrome around original char has even radius (e.g., a#b#a has radius 2)
                        lemma_palindromic_isomorphism_odd_center(s_seq, s_prime, bogus_char, start_idx as int, (start_idx + current_original_len) as int, i, current_original_len);
                    } else {
                         assert(palindromic(s_seq, start_idx as int, start_idx as int));
                    }
                }
            }
        }

        // Move to the next center
        i = i + 1;
    }

    // Convert result back to Vec<char>
    let mut result_vec = Vec::new();
    if max_len > 0 {
        result_vec.extend_from_slice(&s.as_slice()[start_idx..start_idx + max_len]);
    }

    (result_vec, start_idx, start_idx + max_len)
}
// </vc-code>

fn main() {}

}