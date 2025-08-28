function lower(c: char) : bool
    {
        'a' <= c <= 'z'
    }
// pure-end
function upper(c: char) : bool
    {
        'A' <= c <= 'Z'
    }
// pure-end
function alpha(c: char) : bool
    {
        lower(c) || upper(c)
    }
// pure-end
function flip_char(c: char) : (C: char)
        ensures lower(c) <==> upper(C)
        ensures upper(c) <==> lower(C)
    {
        if lower(c) then c - 'a' + 'A' else
        if upper(c) then c + 'a' - 'A' else c
    }
// pure-end
method flip_case(s: string) returns (S: string)
    // post-conditions-start
    ensures |S| == |s|
    ensures forall i :: 0 <= i < |s| ==> (lower(s[i]) <==> upper(S[i]))
    ensures forall i :: 0 <= i < |s| ==> (upper(s[i]) <==> lower(S[i]))
    // post-conditions-end
    {
        // impl-start
        return seq(|s|, i requires 0 <= i < |s| => flip_char(s[i]));
        // impl-end
    }
