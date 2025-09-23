// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 100000 &&
    forall c :: c in s ==> c in {'0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z','A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z','.',',',';'}
}

function SplitString(s: string): seq<string>
    requires |s| >= 1
    ensures |SplitString(s)| >= 1
    ensures forall word :: word in SplitString(s) ==> forall c :: c in word ==> c != ',' && c != ';'
{
    SplitStringHelper(s, 0, 0)
}

function SplitStringHelper(s: string, start: int, pos: int): seq<string>
    requires 0 <= start <= pos <= |s|
    requires forall i :: start <= i < pos ==> s[i] != ',' && s[i] != ';'
    decreases |s| - pos
    ensures |SplitStringHelper(s, start, pos)| >= 1
    ensures forall word :: word in SplitStringHelper(s, start, pos) ==> forall c :: c in word ==> c != ',' && c != ';'
{
    if pos == |s| then
        [s[start..pos]]
    else if s[pos] == ',' || s[pos] == ';' then
        [s[start..pos]] + SplitStringHelper(s, pos + 1, pos + 1)
    else
        SplitStringHelper(s, start, pos + 1)
}

function IsValidInteger(word: string): bool
    ensures IsValidInteger(word) ==> |word| >= 1 && AllDigits(word)
    ensures IsValidInteger(word) ==> (word == "0" || (word[0] >= '1' && word[0] <= '9'))
{
    if |word| == 0 then false
    else if word == "0" then true
    else if |word| >= 1 && word[0] >= '1' && word[0] <= '9' then
        AllDigits(word)
    else false
}

function AllDigits(s: string): bool
    ensures AllDigits(s) ==> forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
{
    if |s| == 0 then true
    else if s[0] >= '0' && s[0] <= '9' then
        AllDigits(s[1..])
    else false
}

function FilterValidIntegers(words: seq<string>): seq<string>
{
    if |words| == 0 then []
    else if IsValidInteger(words[0]) then [words[0]] + FilterValidIntegers(words[1..])
    else FilterValidIntegers(words[1..])
}

function FilterInvalidWords(words: seq<string>): seq<string>
{
    if |words| == 0 then []
    else if !IsValidInteger(words[0]) then [words[0]] + FilterInvalidWords(words[1..])
    else FilterInvalidWords(words[1..])
}

function JoinStrings(words: seq<string>, separator: string): string
    ensures |words| == 0 ==> JoinStrings(words, separator) == ""
    ensures |words| == 1 ==> JoinStrings(words, separator) == words[0]
{
    if |words| == 0 then ""
    else if |words| == 1 then words[0]
    else words[0] + separator + JoinStrings(words[1..], separator)
}
// </vc-preamble>

// <vc-helpers>
lemma FilterValidIntegersConcat(words: seq<string>, i: int)
    requires 0 <= i < |words|
    ensures FilterValidIntegers(words[..i+1]) == 
            if IsValidInteger(words[i]) then FilterValidIntegers(words[..i]) + [words[i]]
            else FilterValidIntegers(words[..i])
{
    assert words[..i+1] == words[..i] + [words[i]];
    FilterValidIntegersConcatHelper(words[..i], [words[i]]);
}

lemma FilterValidIntegersConcatHelper(a: seq<string>, b: seq<string>)
    requires |b| == 1
    ensures FilterValidIntegers(a + b) == 
            if IsValidInteger(b[0]) then FilterValidIntegers(a) + FilterValidIntegers(b)
            else FilterValidIntegers(a)
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        assert a + b == [a[0]] + (a[1..] + b);
        FilterValidIntegersConcatHelper(a[1..], b);
    }
}

lemma FilterInvalidWordsConcat(words: seq<string>, i: int)
    requires 0 <= i < |words|
    ensures FilterInvalidWords(words[..i+1]) == 
            if !IsValidInteger(words[i]) then FilterInvalidWords(words[..i]) + [words[i]]
            else FilterInvalidWords(words[..i])
{
    assert words[..i+1] == words[..i] + [words[i]];
    FilterInvalidWordsConcatHelper(words[..i], [words[i]]);
}

lemma FilterInvalidWordsConcatHelper(a: seq<string>, b: seq<string>)
    requires |b| == 1
    ensures FilterInvalidWords(a + b) == 
            if !IsValidInteger(b[0]) then FilterInvalidWords(a) + FilterInvalidWords(b)
            else FilterInvalidWords(a)
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        assert a + b == [a[0]] + (a[1..] + b);
        FilterInvalidWordsConcatHelper(a[1..], b);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result1: string, result2: string)
    requires ValidInput(s)
    ensures |result1| >= 1 && |result2| >= 1
    ensures (result1 == "-") || (|result1| >= 2 && result1[0] == '"' && result1[|result1|-1] == '"')
    ensures (result2 == "-") || (|result2| >= 2 && result2[0] == '"' && result2[|result2|-1] == '"')
    ensures var words := SplitString(s);
            var validInts := FilterValidIntegers(words);
            var invalidWords := FilterInvalidWords(words);
            (|validInts| == 0 ==> result1 == "-") &&
            (|validInts| > 0 ==> result1 == "\"" + JoinStrings(validInts, ",") + "\"") &&
            (|invalidWords| == 0 ==> result2 == "-") &&
            (|invalidWords| > 0 ==> result2 == "\"" + JoinStrings(invalidWords, ",") + "\"")
// </vc-spec>
// <vc-code>
{
    var words := SplitString(s);

    var validIntegers: seq<string> := [];
    var invalidWords: seq<string> := [];

    for i := 0 to |words|
        invariant 0 <= i <= |words|
        invariant validIntegers == FilterValidIntegers(words[..i])
        invariant invalidWords == FilterInvalidWords(words[..i])
    {
        FilterValidIntegersConcat(words, i);
        FilterInvalidWordsConcat(words, i);

        assert words[..i+1] == words[..i] + [words[i]];
        assert FilterValidIntegers(words[..i+1]) == 
               if IsValidInteger(words[i]) then FilterValidIntegers(words[..i]) + [words[i]]
               else FilterValidIntegers(words[..i]);
        assert FilterInvalidWords(words[..i+1]) == 
               if !IsValidInteger(words[i]) then FilterInvalidWords(words[..i]) + [words[i]]
               else FilterInvalidWords(words[..i]);

        if IsValidInteger(words[i]) {
            validIntegers := validIntegers + [words[i]];
        } else {
            invalidWords := invalidWords + [words[i]];
        }
    }

    assert words[..|words|] == words;
    assert validIntegers == FilterValidIntegers(words);
    assert invalidWords == FilterInvalidWords(words);

    if |validIntegers| == 0 {
        result1 := "-";
    } else {
        var tmpCall1 := JoinStrings(validIntegers, ",");
        result1 := "\"" + tmpCall1 + "\"";
    }

    if |invalidWords| == 0 {
        result2 := "-";
    } else {
        var tmpCall2 := JoinStrings(invalidWords, ",");
        result2 := "\"" + tmpCall2 + "\"";
    }
}
// </vc-code>
