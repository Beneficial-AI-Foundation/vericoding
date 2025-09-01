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
  if |s| == 0 {
    result := "";
  } else {
    result := s + reversed_s[1..];
  }

  // Post-condition proof (informal - Dafny handles formal parts now)
  // Let n = |s|.
  // If n = 0, result = "", which satisfies all post-conditions.
  // If n > 0, |result| = n + (n - 1) = 2n - 1.
  //   |result| <= 2 * |s| holds (2n - 1 <= 2n).
  //   starts_with(result, s) holds by construction (result starts with s).

  // Proof that result is a palindrome: result[k] == result[|result| - 1 - k]
  // Let N = |result| = 2n - 1.

  // Case 1: 0 <= k < n (k is in the original 's' part of result)
  //   result[k] = s[k]
  //   Consider the symmetric index j = N - 1 - k = (2n - 1) - 1 - k = 2n - 2 - k.
  //   Since 0 <= k < n, we have n-1 >= k, so 2n - 2 - k >= 2n - 2 - (n-1) = n - 1.
  //   Also k >= 0, so 2n - 2 - k <= 2n - 2.
  //   Thus, j is in the range [n-1, 2n-2].
  //   If j < n: result[j] = s[j]. We need s[k] == s[j]. This only happens if k=j,
  //     which means k = 2n-2-k => 2k = 2n-2 => k = n-1. This is the center character.
  //     At k = n-1, result[n-1] = s[n-1]. Symmetric index j = 2n-2-(n-1) = n-1. So result[n-1] == result[n-1].
  //   If j >= n: (this is the common case)
  //     Then j is in reversed_s[1..] part. The index within reversed_s is j - n + 1.
  //     result[j] = reversed_s[j - n + 1]
  //               = s[n - 1 - (j - n + 1)]  (by property of reverse_string)
  //               = s[n - 1 - j + n - 1]
  //               = s[2n - 2 - j]
  //     Substitute j = 2n - 2 - k:
  //     result[j] = s[2n - 2 - (2n - 2 - k)] = s[k].
  //     So, result[k] == s[k] and result[j] == s[k]. Therefore, result[k] == result[j].

  // Case 2: n <= k < N (k is in the reversed_s[1..] part of result)
  //   This means k' = k - n + 1 is the index within reversed_s (and k' > 0).
  //   result[k] = reversed_s[k - n + 1]
  //             = s[n - 1 - (k - n + 1)] (by property of reverse_string)
  //             = s[n - 1 - k + n - 1]
  //             = s[2n - 2 - k]
  //   Consider the symmetric index j = N - 1 - k = (2n - 1) - 1 - k = 2n - 2 - k.
  //   Since n <= k < 2n - 1, we have 1 < 2n - 1 - k <= n.
  //   So j is in the range [0, n-1]. This means result[j] = s[j].
  //   We want to show result[k] == result[j], i.e., s[2n - 2 - k] == s[j].
  //   Substitute j = 2n - 2 - k:
  //   s[2n - 2 - k] == s[2n - 2 - k]. This is true.
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