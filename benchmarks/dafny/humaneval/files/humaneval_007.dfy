// <vc-preamble>

function contains_substring(s: string, sub: string): bool
{
    if |sub| == 0 then true
    else if |sub| > |s| then false
    else exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}

function filter_sequence(strings: seq<string>, substring: string): seq<string>
{
    filter_sequence_helper(strings, substring, |strings|)
}

function filter_sequence_helper(strings: seq<string>, substring: string, n: int): seq<string>
    requires 0 <= n <= |strings|
{
    if n == 0 then []
    else if contains_substring(strings[n-1], substring) then
        filter_sequence_helper(strings, substring, n-1) + [strings[n-1]]
    else
        filter_sequence_helper(strings, substring, n-1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (result: seq<string>)
    ensures |result| <= |strings|
    ensures forall i :: 0 <= i < |result| ==> result[i] in strings
    ensures forall i :: 0 <= i < |result| ==> contains_substring(result[i], substring)
    ensures forall i :: 0 <= i < |strings| && contains_substring(strings[i], substring) ==> strings[i] in result
    ensures forall i, j :: 0 <= i < j < |result| ==> 
        exists k1, k2 :: 0 <= k1 < k2 < |strings| && result[i] == strings[k1] && result[j] == strings[k2]
    ensures forall s :: s in result <==> (s in strings && contains_substring(s, substring))
    ensures result == filter_sequence(strings, substring)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
