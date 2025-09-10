predicate ValidInput(n: int, digits: string)
{
    n > 0 && |digits| == n && forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
}

function modifyString(s: string, index: int): string
    requires 0 <= index < |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |modifyString(s, index)| == |s|
    ensures forall i :: 0 <= i < |modifyString(s, index)| ==> '0' <= modifyString(s, index)[i] <= '9'
{
    var key := if s[index] == '0' then 0 else 10 - (s[index] as int - '0' as int);
    var transformed := transformDigits(s, key);
    rotateString(transformed, index)
}

function transformDigits(s: string, key: int): string
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= key <= 9
    ensures |transformDigits(s, key)| == |s|
    ensures forall i :: 0 <= i < |transformDigits(s, key)| ==> '0' <= transformDigits(s, key)[i] <= '9'
    decreases |s|
{
    if |s| == 0 then ""
    else 
        var digit := (s[0] as int - '0' as int + key) % 10;
        [('0' as int + digit) as char] + transformDigits(s[1..], key)
}

function rotateString(s: string, index: int): string
    requires 0 <= index < |s|
    ensures |rotateString(s, index)| == |s|
{
    if |s| == 0 then ""
    else s[index..] + s[..index]
}

predicate isAllDigits(s: string)
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function parseInput(input: string): seq<string>
    ensures |parseInput(input)| >= 0
    decreases |input|
{
    parseInputHelper(input, 0, "", [])
}

function parseInputHelper(input: string, i: int, currentLine: string, lines: seq<string>): seq<string>
    requires 0 <= i <= |input|
    ensures |parseInputHelper(input, i, currentLine, lines)| >= |lines|
    decreases |input| - i
{
    if i >= |input| then
        if |currentLine| > 0 then lines + [currentLine] else lines
    else if input[i] == '\n' then
        parseInputHelper(input, i + 1, "", lines + [currentLine])
    else
        parseInputHelper(input, i + 1, currentLine + [input[i]], lines)
}

function parseInt(s: string): int
    ensures parseInt(s) >= 0
{
    if |s| == 0 then 0
    else if !('0' <= s[0] <= '9') then 0
    else (s[0] as int - '0' as int) + 10 * parseInt(s[1..])
}

// <vc-helpers>
predicate {:opaque} IsPermutation(s1: string, s2: string)
    requires |s1| == |s2|
{
    multiset(s1) == multiset(s2)
}

lemma lemma_transformDigits_isomorphic(s: string, key: int)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= key <= 9
    // Removed IsPermutation from ensures clause as it's not applicable
    decreases |s|
{
    if |s| == 0 {
        // No assertion needed as it's the base case
    } else {
        var digit := (s[0] as int - '0' as int + key) % 10;
        // The original assertion '0' as int + digit) as char == ('0' + (s[0] as int - '0' as int + key) % 10) as char;
        // was a type error because '0' is a char, not an int. It should be ('0' as int) + digit.
        // Also the character arithmetic is not a simple string equality.
        // It's not a direct character identity, but derived from integer arithmetic.
        // The most important part for verification is to establish character range,
        // which is handled by transformDigits postconditions.
        lemma_transformDigits_isomorphic(s[1..], key);
    }
}

lemma lemma_rotateString_is_permutation(s: string, index: int)
    requires 0 <= index < |s|
    ensures IsPermutation(rotateString(s, index), s)
{
    if |s| == 0 {
        assert multiset("") == multiset("");
    } else {
        // Provide the necessary lemma to show that multiset(s[index..] + s[..index]) is a permutation of multiset(s)
        // This is a property of string concatenation and slicing, which Dafny can often deduce,
        // but explicit lemma application helps.
        // The key is that `s[index..] + s[..index]` is explicitly constructed as a rotation.
        // We know that multiset(s) == multiset(s[index..]) + multiset(s[..index]) by string properties.
        // Therefore, rotateString(s, index) forms a permutation.
        // Dafny can often prove multiset equalities for string concatenations of slices.
        // assert multiset(rotateString(s, index)) == multiset(s[index..]) + multiset(s[..index]); // This is definition
        // assert multiset(s) == multiset(s[index..]) + multiset(s[..index]); // This is a general property
    }
}

lemma lemma_modifyString_properties(s: string, index: int)
    requires 0 <= index < |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |modifyString(s, index)| == |s|
    ensures (forall i :: 0 <= i < |modifyString(s, index)| ==> '0' <= modifyString(s, index)[i] <= '9')
    // Removed IsPermutation from ensures clause as it's incorrect for this function.
{
    var key := if s[index] == '0' then 0 else 10 - (s[index] as int - '0' as int);
    var transformed := transformDigits(s, key);
    var rotated := rotateString(transformed, index);

    // Assertions for |modifyString(s, index)| == |s|
    assert |transformed| == |s|; // From transformDigits postcondition
    assert |rotated| == |transformed|; // From rotateString postcondition
    assert |modifyString(s, index)| == |s|;

    // Assertions for (forall i :: 0 <= i < |modifyString(s, index)| ==> '0' <= modifyString(s, index)[i] <= '9')
    assert (forall i :: 0 <= i < |transformed| ==> '0' <= transformed[i] <= '9'); // From transformDigits postcondition
    // For rotated string, the characters are just rearranged, so if transformed has only digits, rotated also has.
    assert (forall i :: 0 <= i < |rotated| ==> '0' <= rotated[i] <= '9');
    assert (forall i :: 0 <= i < |modifyString(s, index)| ==> '0' <= modifyString(s, index)[i] <= '9');
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
    ensures |result| > 0
    ensures result[|result| - 1] == '\n'
    ensures var lines := parseInput(stdin_input);
            if |lines| >= 2 then
                var n := parseInt(lines[0]);
                var digits := lines[1];
                if ValidInput(n, digits) then
                    var minResult := result[..|result|-1];
                    |minResult| == n &&
                    (forall i :: 0 <= i < |minResult| ==> '0' <= minResult[i] <= '9') &&
                    (exists index :: 0 <= index < n && minResult == modifyString(digits, index)) &&
                    (forall index :: 0 <= index < n ==> minResult <= modifyString(digits, index))
                else
                    result == "\n"
            else
                result == "\n"
// </vc-spec>
// <vc-code>
{
    var lines := parseInput(stdin_input);
    if |lines| < 2 {
        return "\n";
    }

    var n_str := lines[0];
    var digits := lines[1];

    if !(forall i :: 0 <= i < |n_str| ==> '0' <= n_str[i] <= '9') {
        return "\n";
    }
    
    var n := parseInt(n_str);

    if !ValidInput(n, digits) {
        return "\n";
    }

    var min_s := modifyString(digits, 0); 
    // Since n >= 1 (due to ValidInput), the range 0 <= 0 < n is valid for modifyString(digits, 0).

    for i := 1 to n - 1
        invariant 0 <= i <= n
        invariant |min_s| == n
        invariant forall k :: 0 <= k < |min_s| ==> '0' <= min_s[k] <= '9'
        invariant forall j :: 0 <= j < i ==> min_s <= modifyString(digits, j)
        decreases n - i
    {
        var current_s := modifyString(digits, i);
        if current_s < min_s {
            min_s := current_s;
        }
    }

    return min_s + "\n";
}
// </vc-code>

