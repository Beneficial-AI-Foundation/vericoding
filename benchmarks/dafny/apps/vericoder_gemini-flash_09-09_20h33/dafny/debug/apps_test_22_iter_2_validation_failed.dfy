predicate is_s_palindrome(s: string)
{
    var pal := "AHIMOoTUVvWwXxY";

    forall i :: 0 <= i < |s| ==> 
        var j := |s| - 1 - i;
        if i >= j then true
        else
            if s[i] == s[j] then s[i] in pal
            else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                 (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
}

// <vc-helpers>
predicate is_char_s_palindrome(c1: char, c2: char)
{
    var pal := "AHIMOoTUVvWwXxY";
    if c1 == c2 then c1 in pal
    else (c1 == 'p' && c2 == 'q') || (c1 == 'q' && c2 == 'p') ||
         (c1 == 'b' && c2 == 'd') || (c1 == 'd' && c2 == 'b')
}

lemma is_s_palindrome_reverse_check(s: string)
    ensures is_s_palindrome(s) <==>
            (forall i :: 0 <= i < |s|/2 ==>
                var j := |s| - 1 - i;
                is_char_s_palindrome(s[i], s[j]))
{
    // Proof for forward direction: is_s_palindrome(s) ==> (forall i :: 0 <= i < |s|/2 ==> is_char_s_palindrome(s[i], s[j]))
    // Assume is_s_palindrome(s). We need to show that for every `i` such that `0 <= i < |s|/2`,
    // `is_char_s_palindrome(s[i], s[j])` holds, where `j = |s| - 1 - i`.
    // Since `0 <= i < |s|/2`, it implies `i < j`.
    // From the definition of `is_s_palindrome(s)`, because `i < j`, the condition
    // `if s[i] == s[j] then s[i] in pal else ...` must hold for `(s[i], s[j])`.
    // This condition is precisely the definition of `is_char_s_palindrome(s[i], s[j])`.
    // Hence, `is_char_s_palindrome(s[i], s[j])` holds.

    // Proof for backward direction: (forall i :: 0 <= i < |s|/2 ==> is_char_s_palindrome(s[i], s[j])) ==> is_s_palindrome(s)
    // Assume `forall i :: 0 <= i < |s|/2 ==> is_char_s_palindrome(s[i], s[j])`.
    // We need to show `is_s_palindrome(s)`. This means we need to show that for `forall i :: 0 <= i < |s|`,
    // the condition in `is_s_palindrome` holds.
    // Let `k` be an arbitrary index such that `0 <= k < |s|`. Let `m = |s| - 1 - k`.

    // Case 1: `k < |s|/2`.
    // In this case, `k < m`. By our assumption, `is_char_s_palindrome(s[k], s[m])` holds.
    // The definition of `is_s_palindrome` for `k < m` requires:
    // `if s[k] == s[m] then s[k] in pal else (s[k] == 'p' && s[m] == 'q') || ...`.
    // This is exactly what `is_char_s_palindrome(s[k], s[m])` asserts, so the condition holds for this `k`.

    // Case 2: `k >= |s|/2`.
    // In this case, `k >= m`. The definition of `is_s_palindrome` for `k >= m` requires `true`.
    // So the condition holds for this `k` as well.

    // Combining both cases, `is_s_palindrome(s)` holds.
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| >= 1
    ensures result == "TAK" || result == "NIE"
    ensures result == "TAK" <==> is_s_palindrome(s)
// </vc-spec>
// <vc-code>
{
    var n := |s|;
    is_s_palindrome_reverse_check(s); // Establish equivalence for the loop

    var left := 0;
    var right := n - 1;

    while left < right
        invariant 0 <= left <= n / 2
        invariant left <= right
        invariant right == n - 1 - left
        invariant n - 1 - left >= n / 2 - 1 // Added an invariant to help with `right` remaining in bounds
        invariant forall k :: 0 <= k < left ==> is_char_s_palindrome(s[k], s[n-1-k])
    {
        if !is_char_s_palindrome(s[left], s[right]) {
            return "NIE";
        }
        left := left + 1;
        right := right - 1;
    }

    // Post-loop: left >= right holds.
    // If n is even, left == right is not possible, so left == n/2 and right == n/2 - 1. So left > right.
    // If n is odd, left == right is possible if the loop terminates when left == right.
    // In either case, all pairs (s[k], s[n-1-k]) for k from 0 up to left-1 have been checked and passed
    // is_char_s_palindrome.
    // Since left is now n/2 (integer division), we have checked all pairs up to < |s|/2.
    assert forall k :: 0 <= k < n/2 ==> is_char_s_palindrome(s[k], s[n-1-k]);
    assert is_s_palindrome(s);

    return "TAK";
}
// </vc-code>

