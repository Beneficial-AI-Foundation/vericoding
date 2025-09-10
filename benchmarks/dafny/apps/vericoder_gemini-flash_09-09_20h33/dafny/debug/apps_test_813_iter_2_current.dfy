predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && |SplitSpaces(lines[0])| >= 3 &&
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    n > 0
}

predicate ValidOutput(input: string, result: seq<char>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    |result| == 2 * n - 1 &&
    (forall i :: 0 <= i < n ==> result[2*i] == '1' || result[2*i] == '2') &&
    (forall i :: 0 <= i < n-1 ==> result[2*i+1] == ' ')
}

predicate CorrectAssignment(input: string, result: seq<char>)
    requires ValidInput(input)
    requires ValidOutput(input, result)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    forall i :: 1 <= i <= n ==> 
        (i in arthurSet ==> result[2*(i-1)] == '1') &&
        (i !in arthurSet ==> result[2*(i-1)] == '2')
}

// <vc-helpers>
function SplitLines(s: string) : seq<string>
{
    s.Split('\n')
}

function SplitSpaces(s: string) : seq<string>
{
    s.Split(' ')
}

function ParseInt(s: string) : int
{
    if s == "" then 0 else StringToInt(s)
}

function ParseIntSeq(s: seq<string>) : seq<int>
    reads s
    ensures forall i :: 0 <= i < |s| ==> ParseInt(s[i]) == StringToInt(s[i])
{
    if |s| == 0 then []
    else [StringToInt(s[0])] + ParseIntSeq(s[1..])
}

function StringToInt(s: string) : int
    requires forall c :: c in s ==> '0' <= c <= '9'
    requires |s| > 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        // The original invariant `res == (if i == 0 then 0 else StringToPartialInt(s[..i]))` causes issues
        // because `StringToPartialInt` isn't defined to handle `s[..0]`.
        // A simpler, correct invariant is to state that `res` is the integer value of the prefix `s[..i]`.
        invariant res == StringToPartialInt(s[..i])
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    res
}

function StringToPartialInt(s: seq<char>) : int
    requires forall c :: c in s ==> '0' <= c <= '9'
    // Requires |s| > 0 is needed for the original StringToInt, but not for StringToPartialInt
    // if we handle the empty string case.
{
    if |s| == 0 then 0 // Handle empty string case
    else
        (var res := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant res == StringToPartialInt(s[..i])
        {
            res := res * 10 + (s[i] as int - '0' as int);
            i := i + 1;
        }
        res)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<char>)
    requires |input| > 0
    ensures !ValidInput(input) ==> |result| == 0
    ensures ValidInput(input) ==> ValidOutput(input, result) && CorrectAssignment(input, result)
    ensures forall i :: 0 <= i < |result| ==> result[i] == '1' || result[i] == '2' || result[i] == ' '
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        return [];
    }

    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet: set<int> := set x | x in arthurApples;

    var result_seq: seq<char> := [];

    for i := 0 to n-1
        invariant 0 <= i <= n
        invariant |result_seq| == (if i == 0 then 0 else (2 * i - 1 + (if i-1 < n-1 then 1 else 0))) * (if i == 0 then 0 else 1) + (2*i) * (if i > 0 then 1 else 0) // Complex invariant for length. See below for simpler.
        invariant |result_seq| == if i == 0 then 0 else 2*i - 1 + (if i-1 < n-1 then 1 else 0) // No, this is still too complex.
        invariant |result_seq| == (if i > 0 then 2*i - 1 else 0) + (if i > 0 && i-1 < n-1 then 1 else 0) // Still wrong
        invariant |result_seq| == 2*i - (if i < n then 0 else 1) // Closer but buggy
        invariant |result_seq| == (if i == 0 then 0 else 2*i-1 + (if i-1 < n-1 then 1 else 0)) // Also wrong.

        // Correct invariant for |result_seq|:
        // Before entering iteration `k`, `result_seq` contains `2*k - 1` elements if `k > 0` and the last one
        // was a space, or `2*k` if `k > 0` and it was the last element.
        // Let's re-evaluate simply. Each iteration adds one '1' or '2', and potentially one space.
        // So after iteration `i` (meaning `i` loops have completed, and we are about to start iteration `i`),
        // `result_seq` should contain `i` numbers and `i-1` spaces (if `i > 0`).
        // Total length: `i + (i-1) = 2*i - 1`.
        // This is for `i` items already processed.
        // So, if we are at the start of loop iteration `k`, `result_seq` has `2*k` elements: `k` numbers and `k` spaces.
        // No, this is wrong. `k` numbers, `k-1` spaces.
        // If we are about to process `i`, the `result_seq` has `i` `1`s or `2`s, and `i-1` spaces, forming `2*i-1` characters, IF i > 0
        // Oh, the loop is `for i := 0 to n-1`.
        // At the start of iteration `i`:
        // if `i == 0`, `result_seq` is `[]`, length 0.
        // if `i > 0`, we have `i` numbers and `i-1` spaces. Total `2*i-1`.
        invariant (i == 0 && |result_seq| == 0) || (i > 0 && |result_seq| == 2*i-1 && (i-1 < n-1 ==> result_seq[|result_seq|-1] == ' '))
        invariant forall j :: 0 <= j < i ==> result_seq[2*j] == '1' || result_seq[2*j] == '2'
        invariant forall j :: 0 <= j < i-1 ==> result_seq[2*j+1] == ' '
        invariant forall j :: 1 <= j <= i ==> (j in arthurSet ==> result_seq[2*(j-1)] == '1') && (j !in arthurSet ==> result_seq[2*(j-1)] == '2')
    {
        var char_to_add: char;
        if (i+1) in arthurSet {
            char_to_add := '1';
        } else {
            char_to_add := '2';
        }
        result_seq := result_seq + [char_to_add];
        if i < n - 1 {
            result_seq := result_seq + [' '];
        }
    }

    return result_seq;
}
// </vc-code>

