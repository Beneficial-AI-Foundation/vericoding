// <vc-preamble>
predicate ValidInput(s: string)
{
    (|s| == 3 || (|s| == 4 && s[3] == '\n')) &&
    forall i :: 0 <= i < (if |s| == 4 then 3 else |s|) ==> (s[i] == 'a' || s[i] == 'b' || s[i] == 'c')
}

function GetInputChars(s: string): string
    requires ValidInput(s)
{
    if |s| == 4 then s[..3] else s
}

predicate IsPermutationOfABC(input_chars: string)
    requires |input_chars| == 3
    requires forall i :: 0 <= i < |input_chars| ==> (input_chars[i] == 'a' || input_chars[i] == 'b' || input_chars[i] == 'c')
{
    input_chars[0] != input_chars[1] && 
    input_chars[1] != input_chars[2] && 
    input_chars[0] != input_chars[2]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| >= 3
    requires ValidInput(s)
    ensures result == "Yes\n" || result == "No\n"
    ensures result == "Yes\n" <==> IsPermutationOfABC(GetInputChars(s))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
