//IMPL 
method allDigits(s: string) returns (result: bool)
ensures result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
{
    result := true;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result <==> (forall j :: 0 <= j < i ==> s[j] in "0123456789")
    {
        if s[i] !in "0123456789" {
            result := false;
            return;
        }
        i := i + 1;
    }
}