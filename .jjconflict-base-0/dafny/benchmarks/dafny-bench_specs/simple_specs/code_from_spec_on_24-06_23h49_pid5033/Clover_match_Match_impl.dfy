//IMPL 
method Match(s: string, p: string) returns (b: bool)
 requires |s| == |p|
 ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
    b := true;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant b <==> forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
    {
        if s[i] != p[i] && p[i] != '?' {
            b := false;
            return;
        }
        i := i + 1;
    }
}