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
lemma split_lines_preserves_structure(s: string)
    ensures var lines := split_lines(s);
            |lines| > 0 ==> (forall i :: 0 <= i < |lines| ==> |lines[i]| >= 0)
{
    // Proof by induction on the structure of s
}

lemma reverse_distributes_over_concat(s1: string, s2: string)
    ensures reverse(s1 + s2) == reverse(s2) + reverse(s1)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert reverse(s1) == "";
        assert reverse(s2) + reverse(s1) == reverse(s2) + "" == reverse(s2);
    } else {
        reverse_distributes_over_concat(s1[1..], s2);
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        assert reverse(s1 + s2) == reverse([s1[0]] + (s1[1..] + s2));
        assert reverse([s1[0]] + (s1[1..] + s2)) == reverse(s1[1..] + s2) + reverse([s1[0]]);
        assert reverse(s1[1..] + s2) == reverse(s2) + reverse(s1[1..]);
        assert reverse([s1[0]]) == [s1[0]];
        assert reverse(s1) == reverse(s1[1..]) + [s1[0]];
    }
}

lemma reverse_involutive(s: string)
    ensures reverse(reverse(s)) == s
{
    if |s| == 0 {
        // Base case: empty string
    } else {
        // Inductive case
        reverse_involutive(s[1..]);
        assert reverse(reverse(s)) == reverse(reverse(s[1..]) + [s[0]]);
        reverse_distributes_over_concat(reverse(s[1..]), [s[0]]);
        assert reverse(reverse(s[1..]) + [s[0]]) == reverse([s[0]]) + reverse(reverse(s[1..]));
        assert reverse([s[0]]) == [s[0]];
        assert reverse(reverse(s[1..])) == s[1..];
        assert [s[0]] + s[1..] == s;
    }
}

lemma reverse_preserves_length(s: string)
    ensures |reverse(s)| == |s|
{
    if |s| == 0 {
        // Base case
    } else {
        // Inductive case
        reverse_preserves_length(s[1..]);
        assert |reverse(s)| == |reverse(s[1..]) + [s[0]]|;
        assert |reverse(s[1..]) + [s[0]]| == |reverse(s[1..])| + 1;
        assert |reverse(s[1..])| == |s[1..]|;
        assert |s[1..]| == |s| - 1;
    }
}

lemma string_equality_decidable(s1: string, s2: string)
    ensures s1 == s2 || s1 != s2
{
    // This is a tautology in classical logic
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
    var normalized_input := stdin_input + if stdin_input[|stdin_input|-1] == '\n' then "" else "\n";
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

