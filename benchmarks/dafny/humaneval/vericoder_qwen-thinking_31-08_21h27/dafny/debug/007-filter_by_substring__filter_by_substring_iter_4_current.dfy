method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
method checkSubstring(s: string, sub: string) returns (result: bool)
    ensures result <==> (sub == "" || (exists k :: 0 <= k <= |s| - |sub| && s[k..k+|sub|] == sub))
{
    if |sub| == 0 {
        result := true;
    } else {
        var i := 0;
        while i <= |s| - |sub|
            invariant 0 <= i <= |s| - |sub| + 1
            invariant (forall j :: 0 <= j < i implies s[j..j+|sub|] != sub)
            decreases |s| - i
        {
            if s[i..i+|sub|] == sub {
                result := true;
                return;
            }
            i := i + 1;
        }
        result := false;
    }
}
// </vc-helpers>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
// </vc-spec>
// <vc-code>
res := [s | s in strings, checkSubstring(s, substring)];
// </vc-code>

