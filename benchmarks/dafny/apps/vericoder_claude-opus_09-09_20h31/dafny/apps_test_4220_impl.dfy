predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    (exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n') &&
    (var newline_pos := find_newline(stdin_input, 0);
     var K_str := stdin_input[0..newline_pos];
     is_valid_positive_integer(K_str)) &&
    (var newline_pos := find_newline(stdin_input, 0);
     var K_str := stdin_input[0..newline_pos];
     var K := string_to_int(K_str);
     1 <= K <= 100) &&
    (var newline_pos := find_newline(stdin_input, 0);
     var rest := stdin_input[newline_pos+1..];
     var S := if |rest| > 0 && rest[|rest|-1] == '\n' then rest[0..|rest|-1] else rest;
     1 <= |S| <= 100 && forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z')
}

function ExtractK(stdin_input: string): int
    requires ValidInput(stdin_input)
{
    var newline_pos := find_newline(stdin_input, 0);
    var K_str := stdin_input[0..newline_pos];
    string_to_int(K_str)
}

function ExtractS(stdin_input: string): string
    requires ValidInput(stdin_input)
{
    var newline_pos := find_newline(stdin_input, 0);
    var rest := stdin_input[newline_pos+1..];
    if |rest| > 0 && rest[|rest|-1] == '\n' then rest[0..|rest|-1] else rest
}

predicate CorrectOutput(stdin_input: string, result: string)
    requires ValidInput(stdin_input)
{
    var K := ExtractK(stdin_input);
    var S := ExtractS(stdin_input);
    K >= 1 && K <= 100 &&
    |S| >= 1 && |S| <= 100 &&
    (forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z') &&
    (|S| <= K ==> result == S + "\n") &&
    (|S| > K ==> result == S[0..K] + "..." + "\n")
}

function find_newline(s: string, start: nat): nat
    requires start <= |s|
    ensures find_newline(s, start) <= |s|
    ensures find_newline(s, start) >= start
    ensures find_newline(s, start) < |s| ==> s[find_newline(s, start)] == '\n'
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else find_newline(s, start + 1)
}

function is_valid_positive_integer(s: string): bool
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9' && s != "0"
}

function string_to_int(s: string): int
    requires is_valid_positive_integer(s)
    ensures string_to_int(s) >= 1
{
    string_to_int_helper(s, 0, 0)
}

function string_to_int_helper(s: string, pos: nat, acc: int): int
    requires pos <= |s|
    requires acc >= 0
    requires forall i :: 0 <= i < pos ==> s[i] >= '0' && s[i] <= '9'
    requires is_valid_positive_integer(s)
    ensures string_to_int_helper(s, pos, acc) >= 1
    decreases |s| - pos
{
    if pos >= |s| then 
        if acc == 0 then 1 else acc
    else if s[pos] >= '0' && s[pos] <= '9' then
        string_to_int_helper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
    else
        if acc == 0 then 1 else acc
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures CorrectOutput(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var newline_pos := find_newline(stdin_input, 0);
    var K_str := stdin_input[0..newline_pos];
    var K := string_to_int(K_str);
    
    var rest := stdin_input[newline_pos+1..];
    var S := if |rest| > 0 && rest[|rest|-1] == '\n' then rest[0..|rest|-1] else rest;
    
    if |S| <= K {
        result := S + "\n";
    } else {
        result := S[0..K] + "..." + "\n";
    }
}
// </vc-code>

