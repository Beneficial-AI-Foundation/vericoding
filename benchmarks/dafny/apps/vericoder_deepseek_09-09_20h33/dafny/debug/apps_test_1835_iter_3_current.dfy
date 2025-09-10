function valid_input_format(input: string): bool
{
    true // Simplified implementation
}

function is_binary_string(s: string): bool
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

function count_test_cases(input: string): nat
    requires valid_input_format(input)
{
    1 // Simplified implementation
}

function count_lines(s: string): nat
{
    1 // Simplified implementation
}

function get_line(s: string, i: nat): string
    requires i < count_lines(s)
{
    "1" // Simplified implementation
}

function get_string_count(input: string, test_case: nat): nat
    requires test_case < count_test_cases(input)
    requires valid_input_format(input)
{
    1 // Simplified implementation
}

function get_test_case_strings(input: string, test_case: nat): seq<string>
    requires test_case < count_test_cases(input)
    requires valid_input_format(input)
    ensures forall s :: s in get_test_case_strings(input, test_case) ==> is_binary_string(s)
{
    ["0"] // Simplified implementation
}

function string_to_int(s: string): int
{
    1 // Simplified implementation
}

function compute_max_palindromes(strings: seq<string>): nat
    requires forall s :: s in strings ==> is_binary_string(s)
    ensures compute_max_palindromes(strings) <= |strings|
    ensures compute_max_palindromes(strings) == greedy_palindrome_count(strings)
{
    greedy_palindrome_count(strings)
}

function palindromic_strings_achievable(strings: seq<string>, k: nat): bool
    requires forall s :: s in strings ==> is_binary_string(s)
    requires k <= |strings|
{
    k <= greedy_palindrome_count(strings)
}

// <vc-helpers>
function greedy_palindrome_count(strings: seq<string>): nat
    requires forall s :: s in strings ==> is_binary_string(s)
{
    if |strings| == 0 then
        0
    else
        var count := 1;
        var last := strings[0];
        var i := 1;
        while i < |strings|
            invariant i <= |strings|
            invariant count >= 1
            invariant count <= i
            invariant forall s :: s in strings ==> is_binary_string(s)
        {
            if strings[i] != last {
                count := count + 1;
                last := strings[i];
            }
            i := i + 1;
        }
        count
}

lemma greedy_palindrome_count_properties(strings: seq<string>)
    requires forall s :: s in strings ==> is_binary_string(s)
    ensures greedy_palindrome_count(strings) <= |strings|
    ensures forall k :: k <= |strings| ==> (k <= greedy_palindrome_count(strings)) == palindromic_strings_achievable(strings, k)
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires input[|input|-1] == '\n'
    requires valid_input_format(input)
    ensures |result| >= 0
    ensures result == "" || result[|result|-1] == '\n'
    ensures count_lines(result) == count_test_cases(input)
    ensures forall i :: 0 <= i < count_test_cases(input) ==> 
        string_to_int(get_line(result, i)) >= 0
    ensures forall i :: 0 <= i < count_test_cases(input) ==> 
        string_to_int(get_line(result, i)) <= get_string_count(input, i)
    ensures forall i :: 0 <= i < count_test_cases(input) ==> 
        string_to_int(get_line(result, i)) == compute_max_palindromes(get_test_case_strings(input, i))
    ensures forall i :: 0 <= i < count_test_cases(input) ==> 
        palindromic_strings_achievable(get_test_case_strings(input, i), string_to_int(get_line(result, i)))
// </vc-spec>
// <vc-code>
{
    var test_case_count := count_test_cases(input);
    var output := "";
    var i := 0;
    
    while i < test_case_count
        invariant 0 <= i <= test_case_count
        invariant |output| >= 0
        invariant output == "" || output[|output|-1] == '\n'
        invariant count_lines(output) == i
        invariant forall j :: 0 <= j < i ==> 
            string_to_int(get_line(output, j)) >= 0
        invariant forall j :: 0 <= j < i ==> 
            string_to_int(get_line(output, j)) <= get_string_count(input, j)
        invariant forall j :: 0 <= j < i ==> 
            string_to_int(get_line(output, j)) == compute_max_palindromes(get_test_case_strings(input, j))
        invariant forall j :: 0 <= j < i ==> 
            palindromic_strings_achievable(get_test_case_strings(input, j), string_to_int(get_line(output, j)))
    {
        var test_strings := get_test_case_strings(input, i);
        var max_palindromes := compute_max_palindromes(test_strings);
        output := output + int_to_string(max_palindromes) + "\n";
        i := i + 1;
    }
    
    result := output;
}
// </vc-code>

