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
lemma modifyStringRotationLemma(s: string, index: int)
    requires 0 <= index < |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures modifyString(s, index) == rotateString(transformDigits(s, 
                            if s[index] == '0' then 0 else 10 - (s[index] as int - '0' as int)), index)
{
}

lemma transformDigitsPreservesAllDigits(s: string, key: int)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= key <= 9
    ensures forall i :: 0 <= i < |transformDigits(s, key)| ==> '0' <= transformDigits(s, key)[i] <= '9'
    decreases |s|
{
    if |s| != 0 {
        transformDigitsPreservesAllDigits(s[1..], key);
    }
}

lemma rotateStringPreservesAllDigits(s: string, index: int)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= index < |s|
    ensures forall i :: 0 <= i < |rotateString(s, index)| ==> '0' <= rotateString(s, index)[i] <= '9'
{
}

lemma modifyStringPreservesAllDigits(s: string, index: int)
    requires 0 <= index < |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures forall i :: 0 <= i < |modifyString(s, index)| ==> '0' <= modifyString(s, index)[i] <= '9'
{
    var key := if s[index] == '0' then 0 else 10 - (s[index] as int - '0' as int);
    transformDigitsPreservesAllDigits(s, key);
    rotateStringPreservesAllDigits(transformDigits(s, key), index);
}

lemma modifyStringHasLength(s: string, index: int)
    requires 0 <= index < |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |modifyString(s, index)| == |s|
{
}

lemma AllModifyStringsValid(s: string, n: int)
    requires n == |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures forall i :: 0 <= i < n ==> 
        |modifyString(s, i)| == n && 
        (forall j :: 0 <= j < n ==> '0' <= modifyString(s, i)[j] <= '9')
{
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> 
            |modifyString(s, j)| == n && 
            (forall k :: 0 <= k < n ==> '0' <= modifyString(s, j)[k] <= '9')
    {
        modifyStringHasLength(s, i);
        modifyStringPreservesAllDigits(s, i);
        i := i + 1;
    }
}

function compareStrings(s1: string, s2: string): bool
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s1| ==> '0' <= s1[i] <= '9'
    requires forall i :: 0 <= i < |s2| ==> '0' <= s2[i] <= '9'
    ensures compareStrings(s1, s2) <==> s1 <= s2
{
    if |s1| == 0 then true
    else if s1[0] < s2[0] then true
    else if s1[0] > s2[0] then false
    else compareStrings(s1[1..], s2[1..])
}

ghost function AllModifyStrings(s: string, n: int): set<string>
    requires n == |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |AllModifyStrings(s, n)| == n
    ensures forall str :: str in AllModifyStrings(s, n) ==> 
        |str| == n && (forall j :: 0 <= j < n ==> '0' <= str[j] <= '9')
{
    AllModifyStringsValid(s, n);
    var i := 0;
    var result_set : set<string> := {};
    while i < n
        invariant 0 <= i <= n
        invariant |result_set| == i
        invariant forall str :: str in result_set ==> 
            |str| == n && (forall j :: 0 <= j < n ==> '0' <= str[j] <= '9')
        invariant result_set == set j | 0 <= j < i :: modifyString(s, j)
    {
        result_set := result_set + {modifyString(s, i)};
        i := i + 1;
    }
    result_set
}

ghost function MinModifyString(s: string, n: int): string
    requires n == |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |MinModifyString(s, n)| == n
    ensures forall j :: 0 <= j < n ==> '0' <= MinModifyString(s, n)[j] <= '9'
    ensures exists i :: 0 <= i < n && MinModifyString(s, n) == modifyString(s, i)
    ensures forall i :: 0 <= i < n ==> MinModifyString(s, n) <= modifyString(s, i)
{
    var all_strings := AllModifyStrings(s, n);
    // Use explicit witness construction instead of :| quantifier
    var min_str := "";
    var first := true;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant first ==> min_str == ""
        invariant !first ==> |min_str| == n && forall j :: 0 <= j < n ==> '0' <= min_str[j] <= '9'
        invariant !first ==> exists j :: 0 <= j < i && min_str == modifyString(s, j)
        invariant !first ==> forall j :: 0 <= j < i ==> min_str <= modifyString(s, j)
    {
        var current := modifyString(s, i);
        if first || compareStrings(current, min_str) {
            min_str := current;
            first := false;
        }
        i := i + 1;
    }
    min_str
}

lemma CompareStringsReflexive(s: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures compareStrings(s, s)
{
    if |s| > 1 {
        CompareStringsReflexive(s[1..]);
    }
}

lemma CompareStringsTransitive(s1: string, s2: string, s3: string)
    requires |s1| == |s2| == |s3|
    requires forall i :: 0 <= i < |s1| ==> '0' <= s1[i] <= '9'
    requires forall i :: 0 <= i < |s2| ==> '0' <= s2[i] <= '9'
    requires forall i :: 0 <= i < |s3| ==> '0' <= s3[i] <= '9'
    requires compareStrings(s1, s2) && compareStrings(s2, s3)
    ensures compareStrings(s1, s3)
{
    if |s1| > 0 {
        if s1[0] < s3[0] {
            // trivial case
        } else if s1[0] > s3[0] {
            // contradiction
        } else {
            CompareStringsTransitive(s1[1..], s2[1..], s3[1..]);
        }
    }
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
    
    if |lines| >= 2 {
        var n := parseInt(lines[0]);
        var digits := lines[1];
        
        if n > 0 && |digits| == n && forall i :: 0 <= i < n ==> '0' <= digits[i] <= '9' {
            var min_result := "";
            var found := false;
            
            var idx := 0;
            while idx < n
                invariant 0 <= idx <= n
                invariant !found ==> min_result == ""
                invariant found ==> |min_result| == n && forall i :: 0 <= i < n ==> '0' <= min_result[i] <= '9'
                invariant found ==> exists i :: 0 <= i < idx && min_result == modifyString(digits, i)
                invariant found ==> forall i :: 0 <= i < idx ==> compareStrings(min_result, modifyString(digits, i))
            {
                var current := modifyString(digits, idx);
                assert |current| == n;
                assert forall i :: 0 <= i < n ==> '0' <= current[i] <= '9';
                
                if !found {
                    min_result := current;
                    found := true;
                    assert compareStrings(min_result, min_result);
                } else {
                    if compareStrings(current, min_result) {
                        min_result := current;
                    } else {
                        assert compareStrings(min_result, current);
                    }
                }
                idx := idx + 1;
            }
            
            result := min_result + "\n";
        } else {
            result := "\n";
        }
    } else {
        result := "\n";
    }
}
// </vc-code>

