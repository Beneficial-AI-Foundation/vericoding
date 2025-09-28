// <vc-preamble>
predicate ValidInputFormat(input: string)
{
    |input| > 0 && 
    exists lines: seq<string> ::
        lines == SplitLines(input) &&
        |lines| >= 1 &&
        IsValidInteger(lines[0]) &&
        var t := StringToInt(lines[0]);
        1 <= t <= 100 &&
        |lines| >= 1 + 3*t &&
        forall i :: 0 <= i < t ==> 
            var base_idx := 1 + 3*i;
            base_idx + 2 < |lines| &&
            IsValidString(lines[base_idx]) &&
            IsValidInteger(lines[base_idx + 1]) &&
            IsValidIntegerArray(lines[base_idx + 2]) &&
            var s := lines[base_idx];
            var m := StringToInt(lines[base_idx + 1]);
            var b_array := ParseIntegerArray(lines[base_idx + 2]);
            1 <= |s| <= 50 &&
            (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z') &&
            1 <= m <= |s| &&
            |b_array| == m &&
            forall k :: 0 <= k < m ==> 0 <= b_array[k] <= 1225
}

predicate ValidOutputFormat(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    |test_cases| > 0 ==> 
    exists output_lines: seq<string> ::
        output_lines == SplitLines(output) &&
        |output_lines| >= |test_cases| &&
        forall i :: 0 <= i < |test_cases| ==> 
            var (s, m, b) := test_cases[i];
            i < |output_lines| &&
            |output_lines[i]| == m &&
            forall j :: 0 <= j < |output_lines[i]| ==> 'a' <= output_lines[i][j] <= 'z'
}

predicate OutputSatisfiesConstraints(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        |t| == m &&
        (forall j :: 0 <= j < m ==> 
            b[j] == SumDistancesToGreaterChars(t, j))
}

predicate PreservesCharacterUsage(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        forall c :: 'a' <= c <= 'z' ==> CountChar(t, c) <= CountChar(s, c)
}

predicate ContainsNewlineTerminatedResults(output: string)
{
    |output| > 0 ==> output[|output|-1] == '\n'
}

function SumDistancesToGreaterChars(t: string, j: int): int
    requires 0 <= j < |t|
{
    SumDistancesToGreaterCharsHelper(t, j, 0)
}

function AbsDiff(i: int, j: int): int
    ensures AbsDiff(i, j) >= 0
    ensures AbsDiff(i, j) == if i >= j then i - j else j - i
{
    if i >= j then i - j else j - i
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed `decreases` clause error by making the argument valid. */
function SumDistancesToGreaterCharsHelper(t: string, j: int, k: int): int
    requires 0 <= j < |t|
    requires 0 <= k <= |t|
    decreases |t| - k
{
    if k == |t| then
        0
    else if t[k] > t[j] then
        AbsDiff(j, k) + SumDistancesToGreaterCharsHelper(t, j, k + 1)
    else
        SumDistancesToGreaterCharsHelper(t, j, k + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    ensures ValidOutputFormat(result, stdin_input)
    ensures OutputSatisfiesConstraints(result, stdin_input)
    ensures PreservesCharacterUsage(result, stdin_input)
    ensures result != "" ==> ContainsNewlineTerminatedResults(result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error where `string` cannot be called on a sequence directly for `t_prefix_array.seq`. Converted `current_output_chars[0 .. k_inner+1]` to `string` explicitly. */
{
    var test_cases := GetTestCases(stdin_input);
    var output_accumulator := new string[|test_cases|];

    for i := 0 to |test_cases| - 1
        invariant 0 <= i <= |test_cases|
        invariant forall k :: 0 <= k < i ==> 
            var (s_k, m_k, b_k) := test_cases[k];
            var t_k := output_accumulator[k];
            |t_k| == m_k && 
            (forall j :: 0 <= j < m_k ==> b_k[j] == SumDistancesToGreaterChars(t_k, j)) &&
            (forall c :: 'a' <= c <= 'z' ==> CountChar(t_k, c) <= CountChar(s_k, c))
    {
        var (s, m, b) := test_cases[i];
        var char_counts := GetCharCounts(s);
        var current_output_chars := new char[m];

        for j := 0 to m - 1
            invariant 0 <= j <= m
            invariant (forall k_inner :: 0 <= k_inner < j ==> 'a' <= current_output_chars[k_inner] <= 'z')
            invariant (forall c :: 'a' <= c <= 'z' ==> CountChar(current_output_chars[0 .. j], c) <= char_counts[c])
            invariant (forall k_inner :: 0 <= k_inner < j ==> 
                var t_prefix_array_seq := current_output_chars[0 .. k_inner+1];
                b[k_inner] == SumDistancesToGreaterChars(string(t_prefix_array_seq), k_inner))
        {
            var best_char := ' '; // Initialize with a dummy value
            var best_char_found := false;

            for c := 'a' to 'z'
                invariant 'a' <= c <= 'z' + 1
            {
                if char_counts[c] > CountChar(current_output_chars[0 .. j], c) {
                    var potential_char := c;
                    var satisfies_constraints := true;

                    var temp_output_chars := new char[j + 1];
                    for k_copy := 0 to j - 1 { temp_output_chars[k_copy] := current_output_chars[k_copy]; }
                    temp_output_chars[j] := potential_char;
                    var t_temp := string(temp_output_chars);

                    if SumDistancesToGreaterChars(t_temp, j) != b[j] {
                        satisfies_constraints := false;
                    }

                    if satisfies_constraints {
                        best_char := potential_char;
                        best_char_found := true;
                        break; 
                    }
                }
            }
            assert best_char_found; 
            current_output_chars[j] := best_char;
        }
        output_accumulator[i] := string(current_output_chars);
    }

    result := ConcatStrings(output_accumulator, "\n");
    if |result| > 0 && result[|result|-1] != '\n' {
        result := result + "\n";
    }
}
// </vc-code>
