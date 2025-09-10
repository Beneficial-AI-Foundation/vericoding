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
lemma palindrome_properties(s: string, i: int, j: int)
    requires 0 <= i <= j < |s|
    requires |s| >= 1
    ensures if i >= j then true
        else
            if s[i] == s[j] then s[i] in "AHIMOoTUVvWwXxY"
            else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                 (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
{
}

lemma mirror_symmetry(s: string, k: int, n: int)
    requires 0 <= k < n
    requires |s| == n
    ensures n - 1 - k == |s| - 1 - k
{
}

ghost function kth_mirror_index(n: int, k: int): (k2: int)
    requires 0 <= k < n
    requires n >= 1
    ensures k2 == n - 1 - k
{
    n - 1 - k
}
// </vc-helpers>
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
    var i := 0;
    var j := n - 1;
    
    while i < j
        invariant 0 <= i <= j + 1 <= n
        invariant i <= n - 1
        invariant j >= 0
        invariant forall k :: 0 <= k < i || j < k < n ==> 
            var k2 := n - 1 - k;
            if k >= k2 then true
            else
                if s[k] == s[k2] then s[k] in "AHIMOoTUVvWwXxY"
                else (s[k] == 'p' && s[k2] == 'q') || (s[k] == 'q' && s[k2] == 'p') ||
                     (s[k] == 'b' && s[k2] == 'd') || (s[k] == 'd' && s[k2] == 'b')
    {
        if s[i] == s[j] {
            if s[i] !in "AHIMOoTUVvWwXxY" {
                result := "NIE";
                return;
            }
        } else {
            if !((s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') 
            || (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')) {
                result := "NIE";
                return;
            }
        }
        
        palindrome_properties(s, i, j);
        
        i := i + 1;
        j := j - 1;
    }
    
    if i == j {
        if s[i] !in "AHIMOoTUVvWwXxY" {
            result := "NIE";
            return;
        }
    }
    
    result := "TAK";
}
// </vc-code>

