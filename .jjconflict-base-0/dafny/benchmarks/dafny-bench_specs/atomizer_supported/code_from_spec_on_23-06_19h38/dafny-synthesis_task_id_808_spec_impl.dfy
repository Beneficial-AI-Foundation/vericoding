//IMPL 
method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{
    result := false;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result <==> k in s[0..i]
    {
        if s[i] == k {
            result := true;
            return;
        }
        i := i + 1;
    }
}