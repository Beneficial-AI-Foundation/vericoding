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
{ }
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
    is_s_palindrome_reverse_check(s); 

    var left := 0;
    var right := n - 1;

    while left < right
        invariant 0 <= left <= n / 2
        invariant left <= right
        invariant right == n - 1 - left
        invariant forall k :: 0 <= k < left ==> is_char_s_palindrome(s[k], s[n-1-k])
        decreases right - left
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

