//IMPL 
method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
    var i := 0;
    var found := false;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant found ==> (exists j :: 0 <= j < i && s[j] == '.' && |s| - j - 1 == 2)
        invariant !found ==> !(exists j :: 0 <= j < i && s[j] == '.' && |s| - j - 1 == 2)
    {
        if s[i] == '.' && |s| - i - 1 == 2 {
            found := true;
        }
        i := i + 1;
    }
    
    result := found;
}