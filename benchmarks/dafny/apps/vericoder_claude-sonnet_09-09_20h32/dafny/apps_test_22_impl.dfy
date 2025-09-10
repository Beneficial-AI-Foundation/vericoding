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
lemma forall_equiv_loop(s: string, i: int)
    requires 0 <= i <= |s|
    ensures (forall k :: i <= k < |s| ==> 
        var j := |s| - 1 - k;
        if k >= j then true
        else
            if s[k] == s[j] then s[k] in "AHIMOoTUVvWwXxY"
            else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
                 (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')) <==>
            (i == |s| && (forall k :: 0 <= k < |s| ==> 
                var j := |s| - 1 - k;
                if k >= j then true
                else
                    if s[k] == s[j] then s[k] in "AHIMOoTUVvWwXxY"
                    else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
                         (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')))
{
    if i == |s| {
        assert forall k {:trigger s[k]} :: i <= k < |s| ==> true by {
            forall k {:trigger s[k]} | i <= k < |s|
                ensures true
            {
                assert i <= k < |s| ==> false;
            }
        }
    }
}

lemma postcondition_helper(s: string)
    requires forall k :: 0 <= k < |s| ==> 
        var j := |s| - 1 - k;
        if k >= j then true
        else
            if s[k] == s[j] then s[k] in "AHIMOoTUVvWwXxY"
            else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
                 (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
    ensures is_s_palindrome(s)
{
}

lemma loop_termination_helper(s: string, i: int)
    requires 0 <= i <= |s|
    requires forall k :: 0 <= k < i ==> 
        var j := |s| - 1 - k;
        if k >= j then true
        else
            if s[k] == s[j] then s[k] in "AHIMOoTUVvWwXxY"
            else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
                 (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
    ensures i == |s| ==> forall k :: 0 <= k < |s| ==> 
        var j := |s| - 1 - k;
        if k >= j then true
        else
            if s[k] == s[j] then s[k] in "AHIMOoTUVvWwXxY"
            else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
                 (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
{
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
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> 
            var j := |s| - 1 - k;
            if k >= j then true
            else
                if s[k] == s[j] then s[k] in pal
                else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
                     (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
    {
        var j := |s| - 1 - i;
        
        if i >= j {
            i := i + 1;
            continue;
        }
        
        if s[i] == s[j] {
            if s[i] !in pal {
                result := "NIE";
                return;
            }
        } else {
            if !((s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                 (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')) {
                result := "NIE";
                return;
            }
        }
        
        i := i + 1;
    }
    
    loop_termination_helper(s, i);
    postcondition_helper(s);
    result := "TAK";
}
// </vc-code>

