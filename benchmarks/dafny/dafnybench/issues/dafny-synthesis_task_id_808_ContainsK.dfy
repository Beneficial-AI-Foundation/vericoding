// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
// </vc-spec>
// <vc-code>
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists j :: 0 <= j < i && s[j] == k)
    {
        if s[i] == k {
            result := true;
            break;
        }
    }
}
// </vc-code>
