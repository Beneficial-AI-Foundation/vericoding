// <vc-preamble>
predicate ValidInputString(input: string)
{
    |input| > 0 && input[|input|-1] == '\n' &&
    1 <= |input|-1 <= 100000 &&
    forall i :: 0 <= i < |input|-1 ==> 'a' <= input[i] <= 'z'
}

predicate CanBeDecomposed(s: string)
{
    CanBeDecomposedReversed(ReverseString(s))
}
// </vc-preamble>

// <vc-helpers>
function ReverseString(s: string): string
{
    if |s| == 0 then ""
    else ReverseString(s[1..]) + [s[0]]
}

predicate CanBeDecomposedReversed(s: string)
{
    if |s| == 0 then true
    else if |s| >= 7 && s[0..7] == "remaerd" then CanBeDecomposedReversed(s[7..])  // reversed "dreamer"
    else if |s| >= 6 && s[0..6] == "resare" then CanBeDecomposedReversed(s[6..])   // reversed "eraser"
    else if |s| >= 5 && s[0..5] == "maerd" then CanBeDecomposedReversed(s[5..])    // reversed "dream"
    else if |s| >= 5 && s[0..5] == "esare" then CanBeDecomposedReversed(s[5..])    // reversed "erase"
    else false
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInputString(input)
    ensures output == "YES\n" || output == "NO\n"
    ensures var s := input[..|input|-1];
            output == "YES\n" <==> CanBeDecomposed(s)
// </vc-spec>
// <vc-code>
{
    var s := input[..|input|-1];
    var reversed_s := ReverseString(s);
    if CanBeDecomposedReversed(reversed_s) {
        output := "YES\n";
    } else {
        output := "NO\n";
    }
}
// </vc-code>
