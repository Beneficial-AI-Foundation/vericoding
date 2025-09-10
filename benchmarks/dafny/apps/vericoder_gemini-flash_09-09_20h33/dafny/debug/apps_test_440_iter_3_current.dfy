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
function RemoveConsecutiveVowels(s: seq<char>): seq<char>
    ensures NoConsecutiveVowels(RemoveConsecutiveVowels(s))
    ensures forall i :: 0 <= i < |RemoveConsecutiveVowels(s)| ==> (exists j :: 0 <= j < |s| && RemoveConsecutiveVowels(s)[i] == s[j])
    ensures |s| > 0 ==> RemoveConsecutiveVowels(s)[0] == s[0]
    ensures |RemoveConsecutiveVowels(s)| <= |s|
{
    if |s| == 0 then
        s
    else if |s| == 1 then
        s
    else if IsVowel(s[0]) && IsVowel(s[1]) then
        RemoveConsecutiveVowels(seq.of(s[0]) + s[2..]) // Remove s[1] and check from s[2] on
    else
        seq.of(s[0]) + RemoveConsecutiveVowels(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(s: seq<char>) returns (result: seq<char>)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    if |s| == 0 then
        result := s;
    else
        result := RemoveConsecutiveVowels(s);
        if |result| == 0 && |s| > 0 then // This case can happen if s contains only consecutive vowels like "aau"
          result := seq.of(s[0]);
        end;
    return result;
}
// </vc-code>

