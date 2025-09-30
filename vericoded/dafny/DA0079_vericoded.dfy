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
lemma NoConsecutiveVowelsPrefix(s: seq<char>, i: int)
    requires 0 <= i <= |s|
    requires NoConsecutiveVowels(s[..i])
    ensures forall j :: 0 <= j < i - 1 ==> !(IsVowel(s[j]) && IsVowel(s[j+1]))
{
    // This follows directly from the definition of NoConsecutiveVowels
}

lemma ExtendNoConsecutiveVowels(s: seq<char>, c: char)
    requires NoConsecutiveVowels(s)
    requires |s| == 0 || !IsVowel(s[|s|-1]) || !IsVowel(c)
    ensures NoConsecutiveVowels(s + [c])
{
    if |s| == 0 {
        assert NoConsecutiveVowels([c]);
    } else {
        forall i | 0 <= i < |s + [c]| - 1
            ensures !(IsVowel((s + [c])[i]) && IsVowel((s + [c])[i+1]))
        {
            if i < |s| - 1 {
                assert (s + [c])[i] == s[i];
                assert (s + [c])[i+1] == s[i+1];
            } else if i == |s| - 1 {
                assert (s + [c])[i] == s[|s|-1];
                assert (s + [c])[i+1] == c;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: seq<char>) returns (result: seq<char>)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
        return [];
    }
    
    result := [s[0]];
    var i := 1;
    
    while i < |s|
        invariant 1 <= i <= |s|
        invariant |result| >= 1
        invariant |result| <= i
        invariant result[0] == s[0]
        invariant NoConsecutiveVowels(result)
    {
        if !IsVowel(result[|result|-1]) || !IsVowel(s[i]) {
            ExtendNoConsecutiveVowels(result, s[i]);
            result := result + [s[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

