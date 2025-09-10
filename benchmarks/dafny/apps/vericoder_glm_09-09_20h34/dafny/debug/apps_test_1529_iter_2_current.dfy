predicate ValidInput(input: string)
{
    |input| >= 0
}

function SplitLines_func(input: string): seq<string>
    requires |input| >= 0
{
    if |input| == 0 then []
    else SplitLines_helper(input, 0, "", [])
}

function SplitLines_helper(input: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |input|
    requires forall j :: 0 <= j < |current| ==> current[j] != '\n'
    decreases |input| - i
{
    if i == |input| then
        if |current| > 0 then acc + [current] else acc
    else if input[i] == '\n' then
        SplitLines_helper(input, i + 1, "", acc + [current])
    else
        SplitLines_helper(input, i + 1, current + [input[i]], acc)
}

function ParseInt_func(s: string): int
    requires |s| >= 0
    ensures ParseInt_func(s) >= 0
{
    if |s| == 0 then 0
    else ParseInt_helper(s, 0, 0)
}

function ParseInt_helper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires acc >= 0
    ensures ParseInt_helper(s, i, acc) >= 0
    decreases |s| - i
{
    if i == |s| || !('0' <= s[i] <= '9') then acc
    else ParseInt_helper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function BuildOutput_func(lines: seq<string>, n: int): string
    requires |lines| > 0
    requires n >= 0
    requires n <= |lines| - 1
{
    if n == 0 then ""
    else if n == 1 then ClassifySentence_func(lines[1])
    else BuildOutput_func(lines, n-1) + "\n" + ClassifySentence_func(lines[n])
}

function ClassifySentence_func(sentence: string): string
{
    if EndsWith_func(sentence, "lala.") && !StartsWith_func(sentence, "miao.") then "Freda's"
    else if StartsWith_func(sentence, "miao.") && !EndsWith_func(sentence, "lala.") then "Rainbow's" 
    else "OMG>.< I don't know!"
}

function StartsWith_func(s: string, prefix: string): bool
    requires |prefix| >= 0
{
    |prefix| <= |s| && (forall i :: 0 <= i < |prefix| ==> s[i] == prefix[i])
}

function EndsWith_func(s: string, suffix: string): bool
    requires |suffix| >= 0
{
    |suffix| <= |s| && (forall i :: 0 <= i < |suffix| ==> s[|s| - |suffix| + i] == suffix[i])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

// <vc-helpers>
lemma SplitLines_helper_terminates(input: string, i: int, current: string, acc: seq<string>)
    requires 0 <= i <= |input|
    requires forall j :: 0 <= j < |current| ==> current[j] != '\n'
    decreases |input| - i
{
    if i < |input| && input[i] != '\n' {
        SplitLines_helper_terminates(input, i + 1, current + [input[i]], acc);
    }
}

lemma SplitLines_func_properties(input: string)
    requires ValidInput(input)
    ensures forall line :: 0 <= line < |SplitLines_func(input)| ==> (forall j :: 0 <= j < |SplitLines_func(input)[line]| ==> SplitLines_func(input)[line][j] != '\n')
{
    if |input| > 0 {
        SplitLines_helper_properties(input, 0, "", []);
    }
}

lemma SplitLines_helper_properties(input: string, i: int, current: string, acc: seq<string>)
    requires 0 <= i <= |input|
    requires forall j :: 0 <= j < |current| ==> current[j] != '\n'
    decreases |input| - i
    ensures forall line :: 0 <= line < |SplitLines_helper(input, i, current, acc)| ==> (forall j :: 0 <= j < |SplitLines_helper(input, i, current, acc)[line]| ==> SplitLines_helper(input, i, current, acc)[line][j] != '\n')
{
    if i == |input| {
        if |current| > 0 {
            var new_acc := acc + [current];
            forall line | 0 <= line < |new_acc|
                ensures forall j | 0 <= j < |new_acc[line]| ==> new_acc[line][j] != '\n'
            {
                if line < |acc| {
                    assert new_acc[line] == acc[line];
                    calc {
                        forall j | 0 <= j < |new_acc[line]| ==> new_acc[line][j] != '\n';
                        { assert new_acc[line] == acc[line]; }
                        forall j | 0 <= j < |acc[line]| ==> acc[line][j] != '\n';
                        true;
                    }
                } else {
                    assert line == |acc|;
                    assert new_acc[line] == current;
                    forall j | 0 <= j < |current| ==> current[j] != '\n';
                }
            }
        }
    } else if input[i] == '\n' {
        var new_acc := acc + [current];
        SplitLines_helper_properties(input, i + 1, "", new_acc);
        forall line | 0 <= line < |SplitLines_helper(input, i, current, acc)|
            ensures forall j | 0 <= j < |SplitLines_helper(input, i, current, acc)[line]| ==> SplitLines_helper(input, i, current, acc)[line][j] != '\n'
        {
            if line == 0 {
                assert SplitLines_helper(input, i, current, acc)[line] == current;
            } else {
                assert SplitLines_helper(input, i, current, acc)[line] == SplitLines_helper(input, i + 1, "", new_acc)[line - 1];
                assert |SplitLines_helper(input, i + 1, "", new_acc)| >= line - 1;
                calc {
                    forall j | 0 <= j < |SplitLines_helper(input, i, current, acc)[line]| ==> SplitLines_helper(input, i, current, acc)[line][j] != '\n';
                    { assert SplitLines_helper(input, i, current, acc)[line] == SplitLines_helper(input, i + 1, "", new_acc)[line - 1]; }
                    forall j | 0 <= j < |SplitLines_helper(input, i + 1, "", new_acc)[line - 1]| ==> SplitLines_helper(input, i + 1, "", new_acc)[line - 1][j] != '\n';
                    true;
                }
            }
        }
    } else {
        SplitLines_helper_properties(input, i + 1, current + [input[i]], acc);
        assert SplitLines_helper(input, i, current, acc) == SplitLines_helper(input, i + 1, current + [input[i]], acc);
    }
}

lemma ParseInt_helper_is_digit(s: string, i: int, acc: int)
    requires 0 <= i <= |s|
    requires acc >= 0
    decreases |s| - i
    ensures i < |s| && '0' <= s[i] <= '9' ==> s[i] as int - '0' as int >= 0 && s[i] as int - '0' as int < 10
{
    if i < |s| && '0' <= s[i] <= '9' {
        assert '0' as int <= s[i] as int <= '9' as int;
        assert 0 <= s[i] as int - '0' as int < 10;
    }
}

lemma StartsWith_transitivity(s: string, prefix: string, subprefix: string)
    requires StartsWith_func(s, prefix)
    requires StartsWith_func(prefix, subprefix)
    ensures StartsWith_func(s, subprefix)
{
    assert |subprefix| <= |s|;
    forall i | 0 <= i < |subprefix|
        ensures s[i] == subprefix[i]
    {
        assert s[i] == prefix[i];
        assert prefix[i] == subprefix[i];
    }
}

lemma EndsWith_transitivity(s: string, suffix: string, subsuffix: string)
    requires EndsWith_func(s, suffix)
    requires EndsWith_func(suffix, subsuffix)
    ensures EndsWith_func(s, subsuffix)
{
    assert |subsuffix| <= |s|;
    assert |subsuffix| <= |suffix|;
    forall i | 0 <= i < |subsuffix|
        ensures s[|s| - |subsuffix| + i] == subsuffix[i]
    {
        calc {
            s[|s| - |subsuffix| + i];
            s[|s| - |suffix| + (|suffix| - |subsuffix| + i)];
            { assert EndsWith_func(s, suffix); assert |suffix| <= |s|; }
            suffix[|suffix| - |subsuffix| + i];
            { assert EndsWith_func(suffix, subsuffix); assert |subsuffix| <= |suffix|; }
            subsuffix[i];
        }
    }
}

lemma BuildOutput_func_inductive(lines: seq<string>, n: int)
    requires |lines| > 0
    requires n >= 0
    requires n <= |lines| - 1
    decreases n
    ensures n == 0 ==> BuildOutput_func(lines, n) == ""
    ensures n == 1 ==> BuildOutput_func(lines, n) == ClassifySentence_func(lines[1])
    ensures n > 1 ==> BuildOutput_func(lines, n) == BuildOutput_func(lines, n-1) + "\n" + ClassifySentence_func(lines[n])
{
    if n == 0 {
        calc {
            BuildOutput_func(lines, 0);
            "";
        }
    } else if n == 1 {
        calc {
            BuildOutput_func(lines, 1);
            ClassifySentence_func(lines[1]);
        }
    } else {
        calc {
            BuildOutput_func(lines, n);
            BuildOutput_func(lines, n-1) + "\n" + ClassifySentence_func(lines[n]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| >= 0
    ensures var lines := SplitLines_func(input); 
            if |lines| == 0 then result == ""
            else (var n := ParseInt_func(lines[0]);
                  result == BuildOutput_func(lines, min(n, |lines| - 1)))
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines_func(input);
    if |lines| == 0 {
        result := "";
    } else {
        var n := ParseInt_func(lines[0]);
        var num_lines_to_process := min(n, |lines| - 1);
        if num_lines_to_process == 0 {
            result := "";
        } else if num_lines_to_process == 1 {
            result := ClassifySentence_func(lines[1]);
        } else {
            result := ClassifySentence_func(lines[1]);
            var i := 2;
            while i <= num_lines_to_process
                invariant 2 <= i <= num_lines_to_process + 1
                invariant result == BuildOutput_func(lines, i - 1)
            {
                result := result + "\n" + ClassifySentence_func(lines[i]);
                i := i + 1;
            }
            assert i == num_lines_to_process + 1;
            assert result == BuildOutput_func(lines, num_lines_to_process);
        }
    }
}
// </vc-code>

