function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
function reverse_string(s: string): string
  ensures |reverse_string(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse_string(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then
    ""
  else
    reverse_string(s[1..]) + s[0..1]
}
// </vc-helpers>

// <vc-spec>
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var reversed_s := reverse_string(s);
  result := s + reversed_s[1..];

  // Proof that result is a palindrome
  // We need to show that for 0 <= k < |result|, result[k] == result[|result| - 1 - k]
  // Let n = |s|
  // |result| = n + (n-1) = 2n - 1 if n > 0
  // |result| = 0 if n = 0

  if |s| == 0 {
    assert is_palindrome(result);
  } else {
    // Case 1: 0 <= k < |s|
    // result[k] = s[k]
    // result[|result| - 1 - k] = result[2*|s| - 1 - 1 - k] = result[2*|s| - 2 - k]
    // _Assume result[k] == result[|result| - 1 - k] for 0 <= k < |s| -- This proof is inductive_
    // Manual proof for understanding:
    // Let n = |s|.
    // result = s + reverse_string(s)[1..]
    // |result| = n + (n-1) = 2n-1 (for n > 0)

    // For 0 <= k < n:
    // result[k] = s[k]

    // We need to show result[k] == result[|result| - 1 - k]
    // Let target_index = |result| - 1 - k
    // target_index = (2n-1) - 1 - k = 2n - 2 - k

    // If 0 <= k < n, then n-1 >= k, so n-1-k >= 0.
    // Also, k < n, so (-k) > (-n), so 2n-2-k > 2n-2-n = n-2.
    // So for k in [0, n-1], target_index is in [n-1, 2n-2].

    // If target_index >= n (i.e., target_index is in the reversed suffix part)
    // Then result[target_index] = reversed_s[target_index - n + 1]
    //                            = s[|s| - 1 - (target_index - n + 1)]
    //                            = s[n - 1 - target_index + n - 1]
    //                            = s[2n - 2 - target_index]
    // We want to show result[k] == s[2n - 2 - target_index]
    // i.e., s[k] == s[2n - 2 - (2n - 2 - k)]
    // i.e., s[k] == s[k]
    // This holds.

    // Case 2: |s| <= k < |result|
    // This is for k' = k - |s| + 1 in 0 <= k' < |s|-1
    // result[k] = reversed_s[k - |s| + 1]
    //           = s[|s| - 1 - (k - |s| + 1)]
    //           = s[|s| - 1 - k + |s| - 1]
    //           = s[2*|s| - 2 - k]

    // Let current_char_index_in_original_s = 2*|s| - 2 - k
    // We need to show result[k] == result[|result| - 1 - k]
    // result[|result| - 1 - k] = result[2*|s| - 1 - 1 - k] = result[2*|s| - 2 - k]

    // Let j = 2*|s| - 2 - k.
    // If j < |s|, then result[j] = s[j].
    // And we have shown result[k] = s[j]. So result[k] == result[j] holds.

    // If j >= |s|, then result[j] = reversed_s[j - |s| + 1]
    //                             = s[|s| - 1 - (j - |s| + 1)]
    //                             = s[2*|s| - 2 - j]
    // Substitute j = 2*|s| - 2 - k:
    // result[j] = s[2*|s| - 2 - (2*|s| - 2 - k)] = s[k]
    // And we have result[k] = s[2*|s| - 2 - k].
    // Does s[2*|s| - 2 - k] == s[k] imply palindrome? No, but it implies result[k] == result[j]

    // The proof depends on the fact that for any k, if result[k] is s[i], then result[|result|-1-k] is also s[i].
  }
}
// </vc-code>

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
  assume{:axiom} false;
}