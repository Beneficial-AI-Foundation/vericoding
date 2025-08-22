//IMPL isPalindrome
method isPalindrome(a: seq<char>) returns (b: bool) 
{
    b := a == a[..|a|];
    // Alternative implementation: b := a == reverse(a);
    // But using sequence slice is more direct in Dafny
    
    // Actually, let me use the reverse comparison for clarity
    var reversed := [];
    var i := |a|;
    while i > 0
        invariant 0 <= i <= |a|
        invariant |reversed| == |a| - i
        invariant forall k :: 0 <= k < |reversed| ==> reversed[k] == a[|a| - 1 - k]
    {
        i := i - 1;
        reversed := reversed + [a[i]];
    }
    b := a == reversed;
}