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
    // Additional proof for is_s_palindrome and is_char_s_palindrome relationship
{
    var pal := "AHIMOoTUVvWwXxY";

    // Forward direction: is_s_palindrome(s) ==> (forall i :: 0 <= i < |s|/2 ==> is_char_s_palindrome(s[i], s[j]))
    // This is essentially directly from the definition.
    // If the full string is a s-palindrome, then for any i up to |s|/2, the condition must hold.
    // The original predicate handles i >= j by returning true, which is equivalent to the chars being s-palindromic
    // for those symmetric pairs where i < j (which is what is_char_s_palindrome checks).

    // Backward direction: (forall i :: 0 <= i < |s|/2 ==> is_char_s_palindrome(s[i], s[j])) ==> is_s_palindrome(s)
    // We need to show that for any i, the condition of is_s_palindrome holds.
    // Case 1: 0 <= i < |s|/2.
    // In this case, 0 <= i < j, and by assumption is_char_s_palindrome(s[i], s[j]) holds.
    // We need to show:
    // (s[i] == s[j] && s[i] in pal) ||
    // (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
    // (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
    // This is precisely the definition of is_char_s_palindrome(s[i], s[j]). So it holds.

    // Case 2: i >= |s|/2.
    // In this case, i >= j (because if i < j, then i < |s|/2).
    // The condition 'if i >= j then true' makes the predicate true for these indices.
    // This matches what we need for is_s_palindrome.
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
    var n := |s];
    is_s_palindrome_reverse_check(s); // Establish equivalence for the loop

    var left := 0;
    var right := n - 1;

    while left < right
        invariant 0 <= left <= n / 2
        invariant left <= right
        invariant n - 1 - left == right // This ensures right is always the symmetric index to left
        invariant forall k :: 0 <= k < left ==> is_char_s_palindrome(s[k], s[n-1-k])
    {
        if !is_char_s_palindrome(s[left], s[right]) {
            return "NIE";
        }
        left := left + 1;
        right := right - 1;
    }

    return "TAK";
}
// </vc-code>

