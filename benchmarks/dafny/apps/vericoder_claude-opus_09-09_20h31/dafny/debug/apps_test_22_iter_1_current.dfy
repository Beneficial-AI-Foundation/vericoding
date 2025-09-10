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
lemma PalindromeCheckCorrect(s: string, k: nat)
    requires k <= |s| / 2
    ensures (forall i :: 0 <= i < k ==> 
        var j := |s| - 1 - i;
        var pal := "AHIMOoTUVvWwXxY";
        if s[i] == s[j] then s[i] in pal
        else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
             (s[i] == 'd' && s[j] == 'b') || (s[i] == 'b' && s[j] == 'd'))
    ==> 
    (forall i :: 0 <= i < |s| ==> 
        var j := |s| - 1 - i;
        if i >= j then true
        else
            var pal := "AHIMOoTUVvWwXxY";
            if s[i] == s[j] then s[i] in pal
            else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                 (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b'))
{
    if k == |s| / 2 {
        forall i | 0 <= i < |s|
            ensures var j := |s| - 1 - i;
                    if i >= j then true
                    else
                        var pal := "AHIMOoTUVvWwXxY";
                        if s[i] == s[j] then s[i] in pal
                        else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                             (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
        {
            var j := |s| - 1 - i;
            if i >= j {
                // trivially true
            } else {
                assert i < |s| / 2;
            }
        }
    }
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
    var pal := "AHIMOoTUVvWwXxY";
    var i := 0;
    var is_pal := true;
    
    while i < |s| / 2
        invariant 0 <= i <= |s| / 2
        invariant is_pal ==> forall k :: 0 <= k < i ==> 
            var j := |s| - 1 - k;
            if s[k] == s[j] then s[k] in pal
            else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
                 (s[k] == 'd' && s[j] == 'b') || (s[k] == 'b' && s[j] == 'd')
    {
        var j := |s| - 1 - i;
        
        if s[i] == s[j] {
            if !(s[i] in pal) {
                is_pal := false;
            }
        } else if (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                  (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b') {
            // valid pair
        } else {
            is_pal := false;
        }
        
        i := i + 1;
    }
    
    if is_pal {
        PalindromeCheckCorrect(s, |s| / 2);
        result := "TAK";
    } else {
        result := "NIE";
    }
}
// </vc-code>

