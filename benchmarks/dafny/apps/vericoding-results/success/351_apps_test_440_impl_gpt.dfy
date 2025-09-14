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
function SkipStartingVowels(s: seq<char>): seq<char>
    ensures |SkipStartingVowels(s)| <= |s|
    ensures |SkipStartingVowels(s)| == 0 || !IsVowel(SkipStartingVowels(s)[0])
    decreases |s|
{
    if |s| == 0 then []
    else if IsVowel(s[0]) then SkipStartingVowels(s[1..])
    else s
}

function FilterNoConsecutiveVowels(s: seq<char>): seq<char>
    decreases |s|
{
    if |s| == 0 then []
    else if |s| == 1 then s
    else
        if IsVowel(s[0]) then
            [s[0]] + FilterNoConsecutiveVowels(SkipStartingVowels(s[1..]))
        else
            [s[0]] + FilterNoConsecutiveVowels(s[1..])
}

lemma SkipHeadNotVowel(s: seq<char>)
    ensures |SkipStartingVowels(s)| == 0 || !IsVowel(SkipStartingVowels(s)[0])
{
    if |s| == 0 {
    } else {
        if IsVowel(s[0]) {
            SkipHeadNotVowel(s[1..]);
        } else {
            assert SkipStartingVowels(s) == s;
        }
    }
}

lemma SkipLenLE(s: seq<char>)
    ensures |SkipStartingVowels(s)| <= |s|
{
    if |s| == 0 {
    } else {
        if IsVowel(s[0]) {
            SkipLenLE(s[1..]);
            assert |SkipStartingVowels(s)| == |SkipStartingVowels(s[1..])|;
            assert |s[1..]| == |s| - 1;
            assert |SkipStartingVowels(s)| <= |s[1..]|;
            assert |s[1..]| <= |s|;
        } else {
            assert SkipStartingVowels(s) == s;
        }
    }
}

lemma NoConsec_Cons(h: char, t: seq<char>)
    requires NoConsecutiveVowels(t)
    requires |t| == 0 || !(IsVowel(h) && IsVowel(t[0]))
    ensures NoConsecutiveVowels([h] + t)
{
    forall i | 0 <= i < |[h] + t| - 1
        ensures !(IsVowel(([h] + t)[i]) && IsVowel(([h] + t)[i+1]))
    {
        if i == 0 {
            if |t| > 0 {
                assert ([h] + t)[0] == h;
                assert ([h] + t)[1] == t[0];
                assert !(IsVowel(h) && IsVowel(t[0]));
            }
        } else {
            assert |[h]| == 1;
            assert i < |[h] + t| - 1 ==> i < 1 + |t| - 1 ==> i < |t|;
            assert 0 < i;
            assert 0 <= i - 1 < |t| - 1;
            assert ([h] + t)[i] == t[i - 1];
            assert ([h] + t)[i + 1] == t[i];
            assert !(IsVowel(t[i - 1]) && IsVowel(t[i]));
        }
    }
}

lemma FilterValid(s: seq<char>)
    ensures ValidOutput(s, FilterNoConsecutiveVowels(s))
    decreases |s|
{
    if |s| == 0 {
        assert |FilterNoConsecutiveVowels(s)| <= |s|;
    } else if |s| == 1 {
        assert FilterNoConsecutiveVowels(s) == s;
        assert |FilterNoConsecutiveVowels(s)| <= |s|;
        assert |FilterNoConsecutiveVowels(s)| > 0;
        assert FilterNoConsecutiveVowels(s)[0] == s[0];
    } else {
        var h := s[0];
        var t := s[1..];
        if IsVowel(h) {
            var t0 := SkipStartingVowels(t);
            // Termination proof for the recursive call
            SkipLenLE(t);
            assert |t0| <= |t|;
            assert |t| == |s| - 1;
            assert |t0| < |s|;
            FilterValid(t0);
            assert NoConsecutiveVowels(FilterNoConsecutiveVowels(t0));
            SkipHeadNotVowel(t);
            // If the filtered tail is non-empty, its head equals t0[0], which is not a vowel
            if |FilterNoConsecutiveVowels(t0)| > 0 {
                assert |t0| > 0; // since FilterNoConsecutiveVowels([]) == []
                assert FilterNoConsecutiveVowels(t0)[0] == t0[0];
                assert !IsVowel(t0[0]);
                assert !IsVowel(FilterNoConsecutiveVowels(t0)[0]);
            }
            NoConsec_Cons(h, FilterNoConsecutiveVowels(t0));
            SkipLenLE(t);
            assert |FilterNoConsecutiveVowels(t0)| <= |t0|;
            assert |t0| <= |t|;
            assert |[h] + FilterNoConsecutiveVowels(t0)| == 1 + |FilterNoConsecutiveVowels(t0)|;
            assert |FilterNoConsecutiveVowels(s)| == 1 + |FilterNoConsecutiveVowels(t0)|;
            assert |FilterNoConsecutiveVowels(s)| <= 1 + |t0|;
            assert 1 + |t0| <= 1 + |t|;
            assert 1 + |t| == |s|;
            assert |FilterNoConsecutiveVowels(s)| <= |s|;
            assert |FilterNoConsecutiveVowels(s)| > 0;
            assert FilterNoConsecutiveVowels(s)[0] == h && h == s[0];
        } else {
            assert |t| < |s|;
            FilterValid(t);
            assert NoConsecutiveVowels(FilterNoConsecutiveVowels(t));
            NoConsec_Cons(h, FilterNoConsecutiveVowels(t));
            assert |FilterNoConsecutiveVowels(t)| <= |t|;
            assert |[h] + FilterNoConsecutiveVowels(t)| == 1 + |FilterNoConsecutiveVowels(t)|;
            assert |FilterNoConsecutiveVowels(s)| == 1 + |FilterNoConsecutiveVowels(t)|;
            assert |FilterNoConsecutiveVowels(s)| <= 1 + |t|;
            assert 1 + |t| == |s|;
            assert |FilterNoConsecutiveVowels(s)| <= |s|;
            assert |FilterNoConsecutiveVowels(s)| > 0;
            assert FilterNoConsecutiveVowels(s)[0] == h && h == s[0];
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
  result := FilterNoConsecutiveVowels(s);
  FilterValid(s);
  assert result == FilterNoConsecutiveVowels(s);
  assert ValidOutput(s, result);
}
// </vc-code>

