// ======= TASK =======
// Find minimum moves for Nastya to collect all coins from n manholes.
// Each manhole starts with one stone on top and one coin underneath.
// Nastya starts at position k and can: throw stones, move adjacent, or collect coins from stone-free manholes.
// Goal is to collect all n coins with minimum moves.

// ======= SPEC REQUIREMENTS =======
predicate validTwoIntegerInput(input: string)
{
    var parts := splitFunction(input, ' ');
    |parts| >= 2 && 
    validIntegerString(parts[0]) && 
    validIntegerString(parts[1]) &&
    stringToIntFunction(parts[0]) >= 2 &&
    1 <= stringToIntFunction(parts[1]) <= stringToIntFunction(parts[0])
}

predicate validIntegerString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function splitFunction(s: string, delimiter: char): seq<string>
    ensures |splitFunction(s, delimiter)| >= 1
{
    if |s| == 0 then [""]
    else 
        var firstDelim := findFirstDelimiter(s, delimiter, 0);
        if firstDelim == -1 then [s]
        else if firstDelim < |s| then [s[..firstDelim]] + splitFunction(s[firstDelim+1..], delimiter)
        else [s]
}

function findFirstDelimiter(s: string, delimiter: char, start: int): int
    requires 0 <= start
    ensures findFirstDelimiter(s, delimiter, start) == -1 || 
            (start <= findFirstDelimiter(s, delimiter, start) < |s|)
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == delimiter then start
    else findFirstDelimiter(s, delimiter, start + 1)
}

function stringToIntFunction(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    stringToIntHelper(s, 0)
}

function stringToIntHelper(s: string, acc: int): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 0 then acc
    else stringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
}

function intToStringFunction(n: int): string
    requires n >= 0
    ensures |intToStringFunction(n)| > 0
{
    if n == 0 then "0"
    else intToStringHelper(n, "")
}

function intToStringHelper(n: int, acc: string): string
    requires n >= 0
    ensures n == 0 ==> intToStringHelper(n, acc) == acc
    ensures n > 0 ==> |intToStringHelper(n, acc)| > |acc|
{
    if n == 0 then acc
    else intToStringHelper(n / 10, [('0' as int + (n % 10)) as char] + acc)
}

// ======= HELPERS =======
method split(s: string, delimiter: char) returns (parts: seq<string>)
    ensures |parts| >= 1
    ensures parts == splitFunction(s, delimiter)
{
    parts := [];
    var current := "";
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant |parts| >= 0
    {
        if s[i] == delimiter {
            parts := parts + [current];
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }

    parts := parts + [current];
    assume parts == splitFunction(s, delimiter);
}

method stringToInt(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result == stringToIntFunction(s)
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
    {
        result := result * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    assume result == stringToIntFunction(s);
}

method intToString(n: int) returns (result: string)
    requires n >= 0
    ensures |result| > 0
    ensures result == intToStringFunction(n)
{
    if n == 0 {
        result := "0";
        return;
    }

    var digits: seq<char> := [];
    var temp := n;

    while temp > 0
        invariant temp >= 0
        invariant |digits| >= 0
    {
        var digit := temp % 10;
        digits := [('0' as int + digit) as char] + digits;
        temp := temp / 10;
    }

    result := "";
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |result| == i
    {
        result := result + [digits[i]];
        i := i + 1;
    }
    assume result == intToStringFunction(n) && |result| > 0;
}

// <vc-helpers>
lemma SplitPreservesLength(s: string, delimiter: char)
    ensures |splitFunction(s, delimiter)| >= 1
{
    // This lemma is automatically proven by the ensures clause of splitFunction
}

lemma ValidInputImpliesPartsLength(input: string)
    requires validTwoIntegerInput(input)
    ensures var parts := splitFunction(input, ' '); |parts| >= 2
{
    // This follows from the definition of validTwoIntegerInput
}

lemma StringToIntPreservation(s: string)
    requires |s| > 0
    requires validIntegerString(s)
    ensures stringToIntFunction(s) == stringToIntFunction(s)
{
    // Trivial lemma for consistency
}

lemma SplitCorrectness(s: string, delimiter: char)
    ensures splitFunction(s, delimiter) == splitFunction(s, delimiter)
{
}

lemma StringToIntNonNegative(s: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures stringToIntFunction(s) >= 0
{
    StringToIntHelperNonNegative(s, 0);
}

lemma StringToIntHelperNonNegative(s: string, acc: int)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires acc >= 0
    ensures stringToIntHelper(s, acc) >= 0
{
    if |s| == 0 {
        // Base case: stringToIntHelper returns acc which is >= 0
    } else {
        var digit := s[0] as int - '0' as int;
        assert 0 <= digit <= 9;
        assert acc * 10 + digit >= 0;
        StringToIntHelperNonNegative(s[1..], acc * 10 + digit);
    }
}

lemma IntToStringCorrectness(n: int)
    requires n >= 0
    ensures intToStringFunction(n) == intToStringFunction(n)
    ensures |intToStringFunction(n)| > 0
{
}

method splitImpl(s: string, delimiter: char) returns (parts: seq<string>)
    ensures |parts| >= 1
    ensures parts == splitFunction(s, delimiter)
    decreases |s|
{
    if |s| == 0 {
        parts := [""];
        return;
    }
    
    var firstDelim := findFirstDelimiterImpl(s, delimiter, 0);
    if firstDelim == -1 {
        parts := [s];
    } else if firstDelim < |s| {
        var restParts := splitImpl(s[firstDelim+1..], delimiter);
        parts := [s[..firstDelim]] + restParts;
    } else {
        parts := [s];
    }
}

method findFirstDelimiterImpl(s: string, delimiter: char, start: int) returns (result: int)
    requires 0 <= start
    ensures result == findFirstDelimiter(s, delimiter, start)
    ensures result == -1 || (start <= result < |s|)
    decreases |s| - start
{
    if start >= |s| {
        result := -1;
    } else if s[start] == delimiter {
        result := start;
    } else {
        result := findFirstDelimiterImpl(s, delimiter, start + 1);
    }
}

method stringToIntImpl(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result == stringToIntFunction(s)
{
    result := stringToIntHelperImpl(s, 0);
}

method stringToIntHelperImpl(s: string, acc: int) returns (result: int)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result == stringToIntHelper(s, acc)
{
    if |s| == 0 {
        result := acc;
    } else {
        var newAcc := acc * 10 + (s[0] as int - '0' as int);
        result := stringToIntHelperImpl(s[1..], newAcc);
    }
}

method intToStringImpl(n: int) returns (result: string)
    requires n >= 0
    ensures |result| > 0
    ensures result == intToStringFunction(n)
{
    if n == 0 {
        result := "0";
        return;
    }
    result := intToStringHelperImpl(n, "");
}

method intToStringHelperImpl(n: int, acc: string) returns (result: string)
    requires n >= 0
    ensures result == intToStringHelper(n, acc)
    ensures n == 0 ==> result == acc
    ensures n > 0 ==> |result| > |acc|
{
    if n == 0 {
        result := acc;
    } else {
        var newAcc := [('0' as int + (n % 10)) as char] + acc;
        result := intToStringHelperImpl(n / 10, newAcc);
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == ' '
    requires validTwoIntegerInput(input)
    ensures |output| > 0
    ensures validTwoIntegerInput(input) ==> 
        (var parts := splitFunction(input, ' ');
         var n := stringToIntFunction(parts[0]);
         var k := stringToIntFunction(parts[1]);
         n >= 2 && 1 <= k <= n ==>
            (if k == 1 || k == n then 
                output == intToStringFunction(3 * n)
            else 
                output == intToStringFunction(3 * n + min(k - 1, n - k))))
// </vc-spec>
// <vc-code>
{
    var parts := splitImpl(input, ' ');
    assert |parts| >= 2;
    
    var n := stringToIntImpl(parts[0]);
    var k := stringToIntImpl(parts[1]);
    
    StringToIntNonNegative(parts[0]);
    StringToIntNonNegative(parts[1]);
    
    var result: int;
    if k == 1 || k == n {
        result := 3 * n;
    } else {
        result := 3 * n + min(k - 1, n - k);
    }
    
    output := intToStringImpl(result);
}
// </vc-code>

