// ======= TASK =======
// Determine if a string is an "s-palindrome" - a string that is symmetric about its middle 
// based on visual mirror reflection of characters. Characters can either be visually identical 
// when mirrored or form valid mirror pairs based on their visual appearance.

// ======= SPEC REQUIREMENTS =======
predicate isSPalindrome(s: string)
{
    var pal := "AHIMOoTUVvWwXxY";
    var fir := "pq";
    var sec := "bd";

    forall i :: 0 <= i < |s| / 2 + 1 ==>
        var l := i;
        var r := |s| - 1 - i;
        if l >= r then true
        else if s[l] == s[r] && charInString(s[l], pal) then true
        else if s[l] == s[r] && !charInString(s[l], pal) then false
        else if s[l] != s[r] && charInString(s[l], fir) && charInString(s[r], fir) then true
        else if s[l] != s[r] && charInString(s[l], sec) && charInString(s[r], sec) then true
        else false
}

// ======= HELPERS =======
function charInString(c: char, str: string): bool
{
    exists i :: 0 <= i < |str| && str[i] == c
}

// <vc-helpers>
lemma sPalindromeEquivalence(s: string)
    ensures isSPalindrome(s) <==> (forall i :: 0 <= i < |s| / 2 ==> sPalindromeCondition(s, i))
{
    if isSPalindrome(s) {
        forall i | 0 <= i < |s| / 2
            ensures sPalindromeCondition(s, i)
        {
            assert 0 <= i < |s| / 2 + 1;
        }
    }
    
    if forall i :: 0 <= i < |s| / 2 ==> sPalindromeCondition(s, i) {
        forall i | 0 <= i < |s| / 2 + 1
            ensures sPalindromeCondition(s, i)
        {
            if i >= |s| / 2 {
                var l := i;
                var r := |s| - 1 - i;
                assert l >= r;
            }
        }
    }
}

predicate sPalindromeCondition(s: string, i: int)
    requires 0 <= i < |s| / 2 + 1
{
    var pal := "AHIMOoTUVvWwXxY";
    var fir := "pq";
    var sec := "bd";
    var l := i;
    var r := |s| - 1 - i;
    if l >= r then true
    else if s[l] == s[r] && charInString(s[l], pal) then true
    else if s[l] == s[r] && !charInString(s[l], pal) then false
    else if s[l] != s[r] && charInString(s[l], fir) && charInString(s[r], fir) then true
    else if s[l] != s[r] && charInString(s[l], sec) && charInString(s[r], sec) then true
    else false
}

lemma LoopMaintainsInvariant(s: string, l: int)
    requires 0 <= l <= |s|
    requires |s| > 0
    ensures 0 <= l < |s| / 2 + 1
{
    if |s| == 1 {
        assert l <= 1;
        assert |s| / 2 + 1 == 1;
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures output == "TAK" || output == "NIE"
    ensures output == "TAK" <==> isSPalindrome(if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input)
// </vc-spec>
// <vc-code>
{
    var s := input;
    if |s| > 0 && s[|s|-1] == '\n' {
        s := s[..|s|-1];
    }

    var pal := "AHIMOoTUVvWwXxY";
    var fir := "pq";
    var sec := "bd";

    var n := |s|;

    if n == 0 {
        output := "TAK";
        return;
    }

    var l := 0;
    var r := n - 1;
    var isPalindrome := true;

    while l < r && isPalindrome
        invariant 0 <= l <= n
        invariant -1 <= r < n
        invariant r == n - 1 - l
        invariant isPalindrome ==> forall i :: 0 <= i < l && i < |s| / 2 ==> sPalindromeCondition(s, i)
        decreases r - l + 1
    {
        if l < |s| / 2 {
            LoopMaintainsInvariant(s, l);
        }
        
        if s[l] == s[r] && charInString(s[l], pal) {
            // Valid symmetric pair
        } else if s[l] == s[r] && !charInString(s[l], pal) {
            // Same character but not symmetric
            isPalindrome := false;
        } else if s[l] != s[r] && charInString(s[l], fir) && charInString(s[r], fir) {
            // Valid mirror pair (pq/bd group 1)
        } else if s[l] != s[r] && charInString(s[l], sec) && charInString(s[r], sec) {
            // Valid mirror pair (bd/pq group 2) 
        } else {
            // Invalid pair
            isPalindrome := false;
        }
        
        l := l + 1;
        r := r - 1;
    }

    if isPalindrome {
        assert forall i :: 0 <= i < |s| / 2 ==> sPalindromeCondition(s, i);
        sPalindromeEquivalence(s);
        output := "TAK";
    } else {
        output := "NIE";
    }
}
// </vc-code>

