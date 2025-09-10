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
lemma PalindromeCheckCorrect(s: string)
    requires |s| >= 1
    ensures (forall i :: 0 <= i < |s| / 2 ==> 
        var j := |s| - 1 - i;
        var pal := "AHIMOoTUVvWwXxY";
        if s[i] == s[j] then s[i] in pal
        else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
             (s[i] == 'd' && s[j] == 'b') || (s[i] == 'b' && s[j] == 'd'))
    ==> 
    is_s_palindrome(s)
{
    assert is_s_palindrome(s) == (
        var pal := "AHIMOoTUVvWwXxY";
        forall i :: 0 <= i < |s| ==> 
            var j := |s| - 1 - i;
            if i >= j then true
            else
                if s[i] == s[j] then s[i] in pal
                else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                     (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
    );
    
    forall i | 0 <= i < |s|
        ensures var j := |s| - 1 - i;
                var pal := "AHIMOoTUVvWwXxY";
                if i >= j then true
                else
                    if s[i] == s[j] then s[i] in pal
                    else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                         (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
    {
        var j := |s| - 1 - i;
        var pal := "AHIMOoTUVvWwXxY";
        if i >= j {
            // trivially true
        } else {
            assert i < j;
            assert j >= |s| / 2;
            assert i < |s| / 2;
            // Now we can use the hypothesis for index i
            assert if s[i] == s[j] then s[i] in pal
                   else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                        (s[i] == 'd' && s[j] == 'b') || (s[i] == 'b' && s[j] == 'd');
        }
    }
}

lemma NotPalindromeHelper(s: string, bad_idx: nat)
    requires |s| >= 1
    requires bad_idx < |s| / 2
    requires var j := |s| - 1 - bad_idx;
             var pal := "AHIMOoTUVvWwXxY";
             !(if s[bad_idx] == s[j] then s[bad_idx] in pal
               else (s[bad_idx] == 'p' && s[j] == 'q') || (s[bad_idx] == 'q' && s[j] == 'p') ||
                    (s[bad_idx] == 'd' && s[j] == 'b') || (s[bad_idx] == 'b' && s[j] == 'd'))
    ensures !is_s_palindrome(s)
{
    var j := |s| - 1 - bad_idx;
    var pal := "AHIMOoTUVvWwXxY";
    
    assert bad_idx < j;
    assert !(if bad_idx >= j then true
             else
                if s[bad_idx] == s[j] then s[bad_idx] in pal
                else (s[bad_idx] == 'p' && s[j] == 'q') || (s[bad_idx] == 'q' && s[j] == 'p') ||
                     (s[bad_idx] == 'b' && s[j] == 'd') || (s[bad_idx] == 'd' && s[j] == 'b'));
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
        invariant !is_pal ==> !is_s_palindrome(s)
    {
        var j := |s| - 1 - i;
        var old_is_pal := is_pal;
        
        if s[i] == s[j] {
            if s[i] in pal {
                // valid same character
            } else {
                is_pal := false;
            }
        } else if (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                  (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b') {
            // valid pair
        } else {
            is_pal := false;
        }
        
        if old_is_pal && !is_pal {
            NotPalindromeHelper(s, i);
        }
        
        i := i + 1;
    }
    
    if is_pal {
        PalindromeCheckCorrect(s);
        result := "TAK";
    } else {
        result := "NIE";
    }
}
// </vc-code>

