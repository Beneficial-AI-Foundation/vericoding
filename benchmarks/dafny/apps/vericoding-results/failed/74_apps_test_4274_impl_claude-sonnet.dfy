predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists lines :: lines == Split(input, '\n') && |lines| > 0 &&
    exists parts :: parts == Split(lines[0], ' ') && |parts| == 2 &&
    exists n, m :: n == StringToInt(parts[0]) && 
                   m == StringToInt(parts[1]) &&
                   1 <= n <= 100 && 0 <= m <= n
}

function ExtractN(input: string): int
requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var parts := Split(lines[0], ' ');
    StringToInt(parts[0])
}

function ExtractM(input: string): int
requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var parts := Split(lines[0], ' ');
    StringToInt(parts[1])
}

predicate CorrectOutput(input: string, result: string)
requires ValidInput(input)
{
    var n := ExtractN(input);
    var m := ExtractM(input);
    (n == m ==> result == "Yes") && (n != m ==> result == "No")
}

// <vc-helpers>
function Split(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then [""]
    else if s[0] == delimiter then [""] + Split(s[1..], delimiter)
    else 
        var rest := Split(s[1..], delimiter);
        if |rest| == 0 then [[s[0]]]
        else [[s[0]] + rest[0]] + rest[1..]
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if s[0] == '0' then 0
        else if s[0] == '1' then 1
        else if s[0] == '2' then 2
        else if s[0] == '3' then 3
        else if s[0] == '4' then 4
        else if s[0] == '5' then 5
        else if s[0] == '6' then 6
        else if s[0] == '7' then 7
        else if s[0] == '8' then 8
        else if s[0] == '9' then 9
        else 0
    else
        StringToInt(s[..|s|-1]) * 10 + StringToInt(s[|s|-1..])
}

lemma SplitProperties(input: string)
requires ValidInput(input)
ensures var lines := Split(input, '\n'); |lines| > 0
ensures var lines := Split(input, '\n'); var parts := Split(lines[0], ' '); |parts| == 2
ensures var lines := Split(input, '\n'); var parts := Split(lines[0], ' '); 
        var n := StringToInt(parts[0]); var m := StringToInt(parts[1]); 
        1 <= n <= 100 && 0 <= m <= n
{
    var lines := Split(input, '\n');
    var parts := Split(lines[0], ' ');
    var n := StringToInt(parts[0]);
    var m := StringToInt(parts[1]);
    assert exists lines' :: lines' == Split(input, '\n') && |lines'| > 0 &&
           (exists parts' :: parts' == Split(lines'[0], ' ') && |parts'| == 2 &&
            (exists n', m' :: 
             n' == StringToInt(parts'[0]) && m' == StringToInt(parts'[1]) &&
             1 <= n' <= 100 && 0 <= m' <= n'));
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures CorrectOutput(input, result)
ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
    SplitProperties(input);
    var n := ExtractN(input);
    var m := ExtractM(input);
    
    if n == m {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

