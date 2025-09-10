predicate ValidInput(lines: seq<string>)
{
    |lines| >= 2 && |lines[0]| > 0 && |lines[1]| > 0
}

predicate IsSymmetric(first_row: string, second_row: string)
{
    reverse(first_row) == second_row
}

function split_lines(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + split_lines(s[1..])
    else 
        var rest := split_lines(s[1..]);
        if |rest| == 0 then [[s[0]]]
        else [rest[0] + [s[0]]] + rest[1..]
}

function reverse(s: string): string
{
    if |s| == 0 then ""
    else reverse(s[1..]) + [s[0]]
}

// <vc-helpers>
lemma lemma_split_lines_length(s: string)
    ensures |split_lines(s)| > 0 || |s| == 0
{
    if |s| > 0 {
        if s[0] == '\n' {
            lemma_split_lines_length(s[1..]);
        } else {
            lemma_split_lines_length(s[1..]);
        }
    }
}

lemma lemma_reverse_length(s: string)
    ensures |reverse(s)| == |s|
{
    if |s| == 0 {
    } else {
        lemma_reverse_length(s[1..]);
    }
}

lemma lemma_reverse_involutive(s: string)
    ensures reverse(reverse(s)) == s
{
    if |s| == 0 {
    } else {
        lemma_reverse_involutive(s[1..]);
        calc {
            reverse(reverse(s));
            reverse(reverse(s[1..]) + [s[0]]);
            [s[0]] + reverse(reverse(s[1..]));
            [s[0]] + s[1..];
            s;
        }
    }
}

lemma lemma_split_lines_append_empty(s: string)
    ensures split_lines("" + s) == split_lines(s)
{
}

lemma lemma_split_lines_newline_prefix(s: string)
    ensures s[0] == '\n' ==> split_lines(['\n'] + s) == [""] + split_lines(s)
{
}

lemma lemma_split_lines_append(s1: string, s2: string)
    ensures split_lines(s1 + s2) == split_lines(s1) + split_lines(s2)
    decreases |s1|
{
    if |s1| == 0 {
        lemma_split_lines_append_empty(s2);
    } else if s1[0] == '\n' {
        var s1_rest := s1[1..];
        lemma_split_lines_append(s1_rest, s2);
        lemma_split_lines_newline_prefix(s1_rest + s2);
    } else {
        var s1_rest := s1[1..];
        lemma_split_lines_append(s1_rest, s2);
        
        if |split_lines(s1_rest + s2)| == 0 {
            assert split_lines(s1_rest + s2) == [];
            assert |s1_rest + s2| == 0;
            assert |s1_rest| == 0 && |s2| == 0;
        } else {
            // Let Dafny use the inductive hypothesis
        }
    }
}

function get_lines(s: string): seq<string>
{
    split_lines(s)
}

lemma lemma_get_lines_length(s: string)
    requires |s| > 0
    ensures |get_lines(s)| > 0
{
    lemma_split_lines_length(s);
}

lemma lemma_last_char_newline_property(s: string)
    ensures (s + if |s| > 0 && s[|s|-1] == '\n' then "" else "\n") == if |s| > 0 && s[|s|-1] == '\n' then s else s + "\n"
{
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures result == "YES\n" || result == "NO\n"
    ensures var normalized_input := stdin_input + if stdin_input[|stdin_input|-1] == '\n' then "" else "\n";
            var lines := split_lines(normalized_input);
            ValidInput(lines) ==> (result == "YES\n" <==> IsSymmetric(lines[0], lines[1]))
    ensures var normalized_input := stdin_input + if stdin_input[|stdin_input|-1] == '\n' then "" else "\n";
            var lines := split_lines(normalized_input);
            !ValidInput(lines) ==> result == "NO\n"
// </vc-spec>
// <vc-code>
{
    var normalized_input := stdin_input + (if |stdin_input| > 0 && stdin_input[|stdin_input|-1] == '\n' then "" else "\n");
    var lines := split_lines(normalized_input);
    
    if |lines| >= 2 && |lines[0]| > 0 && |lines[1]| > 0 {
        if reverse(lines[0]) == lines[1] {
            result := "YES\n";
        } else {
            result := "NO\n";
        }
    } else {
        result := "NO\n";
    }
}
// </vc-code>

