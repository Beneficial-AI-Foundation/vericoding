// ======= TASK =======
// Given a phone number, determine if there exists another phone number with the same sequence 
// of finger movements on a standard phone keypad. Return "YES" if the number has unique finger 
// movements, "NO" if another number exists with the same movements.

// ======= SPEC REQUIREMENTS =======
function FindFirstNewline(s: string): int
    requires |s| > 0
    requires '\n' in s
    ensures 0 <= FindFirstNewline(s) < |s|
    ensures s[FindFirstNewline(s)] == '\n'
    ensures forall i :: 0 <= i < FindFirstNewline(s) ==> s[i] != '\n'
{
    if s[0] == '\n' then 0
    else 1 + FindFirstNewline(s[1..])
}

function ExtractDigits(input: string): seq<int>
    requires |input| > 0
    requires '\n' in input
    requires exists i :: 0 <= i < |input| && input[i] == '\n' && i + 1 < |input|
    requires var newlinePos := FindFirstNewline(input); 
             newlinePos + 1 < |input| && 
             forall j :: newlinePos + 1 <= j < |input| ==> '0' <= input[j] <= '9'
{
    var newlinePos := FindFirstNewline(input);
    var phoneNumber := input[newlinePos + 1..];
    assert |phoneNumber| > 0;
    seq(|phoneNumber|, i requires 0 <= i < |phoneNumber| => phoneNumber[i] as int - '0' as int)
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    '\n' in input &&
    (exists i :: 0 <= i < |input| && input[i] == '\n' && i + 1 < |input|) &&
    var newlinePos := FindFirstNewline(input);
    newlinePos + 1 < |input| && 
    forall j :: newlinePos + 1 <= j < |input| ==> '0' <= input[j] <= '9'
}

predicate HasUniqueMovements(digits: seq<int>)
{
    var hasLeft := 1 in digits || 4 in digits || 7 in digits || 0 in digits;
    var hasTop := 1 in digits || 2 in digits || 3 in digits;
    var hasRight := 3 in digits || 6 in digits || 9 in digits || 0 in digits;
    var hasBottom := 7 in digits || 0 in digits || 9 in digits;
    hasLeft && hasTop && hasRight && hasBottom
}

// <vc-helpers>
method SplitByNewline(s: string) returns (lines: seq<string>)
    ensures |lines| >= 1
    ensures forall line :: line in lines ==> '\n' !in line
{
    lines := [];
    var current := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall line :: line in lines ==> '\n' !in line
        invariant '\n' !in current
    {
        if s[i] == '\n' {
            lines := lines + [current];
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    lines := lines + [current];
}

method ParseInt(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
    {
        result := result * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
}

lemma ExtractDigitsEquivalence(input: string, digits: seq<int>)
    requires ValidInput(input)
    requires var newlinePos := FindFirstNewline(input);
             var phoneNumber := input[newlinePos + 1..];
             |digits| == |phoneNumber| &&
             forall k :: 0 <= k < |phoneNumber| ==> digits[k] == phoneNumber[k] as int - '0' as int
    ensures digits == ExtractDigits(input)
{
    var newlinePos := FindFirstNewline(input);
    var phoneNumber := input[newlinePos + 1..];
    var extractedDigits := ExtractDigits(input);
    
    assert |digits| == |phoneNumber| == |extractedDigits|;
    
    forall k | 0 <= k < |phoneNumber|
        ensures digits[k] == extractedDigits[k]
    {
        assert digits[k] == phoneNumber[k] as int - '0' as int;
        assert extractedDigits[k] == phoneNumber[k] as int - '0' as int;
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures output == "YES" || output == "NO"
    ensures output == "YES" <==> HasUniqueMovements(ExtractDigits(input))
// </vc-spec>
// <vc-code>
{
    var newlinePos := FindFirstNewline(input);
    var phoneNumber := input[newlinePos + 1..];

    var digits: seq<int> := [];
    var i := 0;
    while i < |phoneNumber|
        invariant 0 <= i <= |phoneNumber|
        invariant |digits| == i
        invariant forall k :: 0 <= k < i ==> digits[k] == phoneNumber[k] as int - '0' as int
    {
        var digit := phoneNumber[i] as int - '0' as int;
        digits := digits + [digit];
        i := i + 1;
    }

    ExtractDigitsEquivalence(input, digits);
    assert digits == ExtractDigits(input);

    var hasLeft := 1 in digits || 4 in digits || 7 in digits || 0 in digits;
    var hasTop := 1 in digits || 2 in digits || 3 in digits;
    var hasRight := 3 in digits || 6 in digits || 9 in digits || 0 in digits;
    var hasBottom := 7 in digits || 0 in digits || 9 in digits;

    if hasLeft && hasTop && hasRight && hasBottom {
        output := "YES";
    } else {
        output := "NO";
    }
}
// </vc-code>

