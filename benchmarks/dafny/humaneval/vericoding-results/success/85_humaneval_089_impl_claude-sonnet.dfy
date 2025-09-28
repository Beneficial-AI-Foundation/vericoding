// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method encrypt(s: string) returns (result: string)
    requires |s| >= 0
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> (
        if 'a' <= s[i] <= 'z' then
            result[i] == (((s[i] as int - 'a' as int + 4) % 26) + 'a' as int) as char
        else if 'A' <= s[i] <= 'Z' then
            result[i] == (((s[i] as int - 'A' as int + 4) % 26) + 'A' as int) as char
        else
            result[i] == s[i]
    )
// </vc-spec>
// <vc-code>
{
    result := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> (
            if 'a' <= s[j] <= 'z' then
                result[j] == (((s[j] as int - 'a' as int + 4) % 26) + 'a' as int) as char
            else if 'A' <= s[j] <= 'Z' then
                result[j] == (((s[j] as int - 'A' as int + 4) % 26) + 'A' as int) as char
            else
                result[j] == s[j]
        )
    {
        var c := s[i];
        var encrypted_char: char;
        
        if 'a' <= c <= 'z' {
            encrypted_char := (((c as int - 'a' as int + 4) % 26) + 'a' as int) as char;
        } else if 'A' <= c <= 'Z' {
            encrypted_char := (((c as int - 'A' as int + 4) % 26) + 'A' as int) as char;
        } else {
            encrypted_char := c;
        }
        
        result := result + [encrypted_char];
        i := i + 1;
    }
}
// </vc-code>
