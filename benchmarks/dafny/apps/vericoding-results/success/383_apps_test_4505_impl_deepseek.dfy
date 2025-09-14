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

// <vc-helpers>
lemma ThreeDistinctCharsArePermutationOfABC(chars: string)
    requires |chars| == 3
    requires forall i :: 0 <= i < 3 ==> (chars[i] == 'a' || chars[i] == 'b' || chars[i] == 'c')
    ensures IsPermutationOfABC(chars) <==> (chars[0] != chars[1] && chars[1] != chars[2] && chars[0] != chars[2])
{
}

lemma PermutationCheck(chars: string)
    requires |chars| == 3
    requires forall i :: 0 <= i < 3 ==> (chars[i] == 'a' || chars[i] == 'b' || chars[i] == 'c')
    ensures IsPermutationOfABC(chars) == (chars[0] != chars[1] && chars[1] != chars[2] && chars[0] != chars[2])
{
}
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
    var inputChars := GetInputChars(s);
    if inputChars[0] != inputChars[1] && inputChars[1] != inputChars[2] && inputChars[0] != inputChars[2] {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

