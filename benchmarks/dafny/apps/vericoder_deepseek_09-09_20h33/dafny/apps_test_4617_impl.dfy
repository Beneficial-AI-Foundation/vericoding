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
            { assert s == [s[0]] + s[1..]; }
            reverse(reverse(s[1..]) + [s[0]]);
            { lemma_reverse_append(reverse(s[1..]), [s[0]]); }
            reverse([s[0]]) + reverse(reverse(s[1..]));
            { assert reverse([s[0]]) == [s[0]]; lemma_reverse_involutive(s[1..]); }
            [s[0]] + s[1..];
            s;
        }
    }
}

lemma lemma_reverse_append(s1: string, s2: string)
    ensures reverse(s1 + s2) == reverse(s2) + reverse(s1)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert reverse(s2) == reverse(s2) + "";
    } else {
        lemma_reverse_append(s1[1..], s2);
        assert reverse(s1 + s2) == reverse((s1[1..] + s2) + [s1[0]]) == [s1[0]] + reverse(s1[1..] + s2);
        assert [s1[0]] + (reverse(s2) + reverse(s1[1..])) == (reverse(s2) + [s1[0]]) + reverse(s1[1..]);
        assert reverse(s2) + reverse(s1) == reverse(s2) + (reverse(s1[1..]) + [s1[0]]);
    }
}

lemma lemma_split_lines_append(s1: string, s2: string)
    ensures split_lines(s1 + s2) == split_lines(s1) + split_lines(s2)
    decreases |s1|
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert split_lines(s1) == [];
    } else if s1[0] == '\n' {
        var s1_rest := s1[1..];
        lemma_split_lines_append(s1_rest, s2);
        calc {
            split_lines(s1 + s2);
            split_lines(['\n'] + (s1_rest + s2));
            [""] + split_lines(s1_rest + s2);
            { lemma_split_lines_append(s1_rest, s2); }
            [""] + (split_lines(s1_rest) + split_lines(s2));
            ([""] + split_lines(s1_rest)) + split_lines(s2);
            split_lines(s1) + split_lines(s2);
        }
    } else {
        var s1_rest := s1[1..];
        lemma_split_lines_append(s1_rest, s2);
        var rest_lines := split_lines(s1_rest + s2);
        if |rest_lines| == 0 {
            assert |s1_rest + s2| == 0;
            assert |s1_rest| == 0 && |s2| == 0;
            assert split_lines(s1 + s2) == [[s1[0]]];
            assert split_lines(s1) == [[s1[0]]];
            assert split_lines(s2) == [];
        } else {
            calc {
                split_lines(s1 + s2);
                [split_lines(s1_rest + s2)[0] + [s1[0]]] + split_lines(s1_rest + s2)[1..];
                { lemma_split_lines_append(s1_rest, s2); }
                [(split_lines(s1_rest) + split_lines(s2))[0] + [s1[0]]] + (split_lines(s1_rest) + split_lines(s2))[1..];
                [split_lines(s1_rest)[0] + [s1[0]]] + (split_lines(s1_rest)[1..] + split_lines(s2));
                ([split_lines(s1_rest)[0] + [s1[0]]] + split_lines(s1_rest)[1..]) + split_lines(s2);
                split_lines(s1) + split_lines(s2);
            }
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
    var has_newline := |stdin_input| > 0 && stdin_input[|stdin_input|-1] == '\n';
    var normalized_input := stdin_input + (if has_newline then "" else "\n");
    var lines := split_lines(normalized_input);
    
    if |lines| >= 2 && |lines[0]| > 0 && |lines[1]| > 0 {
        assert ValidInput(lines);
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

