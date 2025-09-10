predicate IsVowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y'
}

predicate NoConsecutiveVowels(s: seq<char>)
{
    forall i :: 0 <= i < |s| - 1 ==> !(IsVowel(s[i]) && IsVowel(s[i+1]))
}

predicate ValidOutput(input: seq<char>, output: seq<char>)
{
    |output| <= |input| &&
    NoConsecutiveVowels(output) &&
    (|input| > 0 ==> |output| > 0) &&
    (|input| > 0 ==> output[0] == input[0])
}

// <vc-helpers>
lemma EmptySeqValid()
    ensures ValidOutput([], [])
{
}

lemma SingleCharValid(c: char)
    ensures ValidOutput([c], [c])
{
}

lemma NoConsecutiveVowelsPreserved(s: seq<char>, i: int)
    requires 0 <= i < |s|
    requires NoConsecutiveVowels(s[..i+1])
    requires i == 0 || !IsVowel(s[i-1]) || !IsVowel(s[i])
    ensures NoConsecutiveVowels(s[..i+1])
{
}

lemma ValidOutputExtension(input: seq<char>, output: seq<char>, newChar: char)
    requires ValidOutput(input, output)
    requires |output| < |input|
    requires newChar == input[|output|]
    requires |output| == 0 || !IsVowel(output[|output|-1]) || !IsVowel(newChar)
    ensures ValidOutput(input, output + [newChar])
{
    var newOutput := output + [newChar];
    assert |newOutput| <= |input|;
    assert |input| > 0 ==> |newOutput| > 0;
    assert |input| > 0 ==> newOutput[0] == input[0];
    
    forall i | 0 <= i < |newOutput| - 1
        ensures !(IsVowel(newOutput[i]) && IsVowel(newOutput[i+1]))
    {
        if i < |output| - 1 {
            assert !(IsVowel(newOutput[i]) && IsVowel(newOutput[i+1]));
        } else if i == |output| - 1 {
            assert newOutput[i] == output[|output|-1];
            assert newOutput[i+1] == newChar;
            assert !(IsVowel(newOutput[i]) && IsVowel(newOutput[i+1]));
        }
    }
}

lemma ValidOutputSkip(input: seq<char>, output: seq<char>, skipPos: int)
    requires ValidOutput(input, output)
    requires |output| < |input|
    requires 0 <= skipPos < |input|
    requires skipPos >= |output|
    ensures ValidOutput(input, output)
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: seq<char>) returns (result: seq<char>)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
        EmptySeqValid();
        return [];
    }
    
    result := [s[0]];
    SingleCharValid(s[0]);
    
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant ValidOutput(s, result)
        invariant |result| >= 1
        invariant result[0] == s[0]
        invariant |result| <= i
    {
        if |result| == 0 || !IsVowel(result[|result|-1]) || !IsVowel(s[i]) {
            if |result| < |s| {
                ValidOutputExtension(s[..i+1], result, s[i]);
                result := result + [s[i]];
            }
        }
        i := i + 1;
    }
}
// </vc-code>

