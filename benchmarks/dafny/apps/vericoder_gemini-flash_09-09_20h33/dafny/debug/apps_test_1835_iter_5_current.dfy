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
function is_palindrome(s: string): bool
    ensures is_palindrome(s) <==> (s == s.rev())
{
    s == s.rev()
}

function char_to_int(c: char): int
    requires c == '0' || c == '1'
    ensures char_to_int(c) == 0 || char_to_int(c) == 1
{
    if c == '0' then 0 else 1
}

function string_to_nat(s: string): nat
    requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
    ensures string_to_nat(s) >= 0
{
    if |s| == 0 then
        0
    else
        var res := 0;
        for i := 0 to |s| - 1
        {
            res := res * 10 + ((s[i] as int) - ('0' as int));
        }
        res
}

function {:id "greedy_palindrome_count"} greedy_palindrome_count(strings: seq<string>): nat
    requires forall s :: s in strings ==> is_binary_string(s)
    ensures greedy_palindrome_count(strings) <= |strings|
{
    var count := 0;
    var used_indices: set<nat> := {};
    for i := 0 to |strings| - 1
        decreases |strings| - i
        invariant 0 <= i <= |strings|
        invariant count <= |strings|
        invariant forall k :: k in used_indices ==> 0 <= k < |strings|
        invariant count == |used_indices|
        invariant forall j :: j in used_indices ==> is_palindrome(strings[j])
        invariant forall j :: 0 <= j < i && !(j in used_indices) ==> !is_palindrome(strings[j])
    {
        if is_palindrome(strings[i]) && !(i in used_indices) {
            count := count + 1;
            used_indices := used_indices + {i};
        }
    }
    count
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
    var num_test_cases := count_test_cases(input);
    var results: seq<string> := [];

    for i := 0 to num_test_cases - 1
        invariant 0 <= i <= num_test_cases
        invariant |results| == i
        invariant forall k :: 0 <= k < |results| ==>
            var current_result_int := string_to_int(results[k]);
            var current_strings := get_test_case_strings(input, k);
            (forall s :: s in current_strings ==> is_binary_string(s)) &&
            current_result_int >= 0 &&
            current_result_int <= get_string_count(input, k) &&
            current_result_int == compute_max_palindromes(current_strings) &&
            palindromic_strings_achievable(current_strings, current_result_int)
    {
        var current_strings := get_test_case_strings(input, i);
        var max_palindromes := compute_max_palindromes(current_strings);
        results := results + [ (max_palindromes as string) ];
    }

    result := "";
    for i := 0 to |results| - 1
        invariant 0 <= i <= |results|
        invariant result == "".Join(results[..i].map(s => s + "\n"))
    {
        result := result + results[i] + "\n";
    }
    return result;
}
// </vc-code>

