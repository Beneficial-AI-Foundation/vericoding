// <vc-preamble>
// Helper predicate to check if a character is alphanumeric
predicate isAlphaNumeric(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z') || ('0' <= c <= '9')
}

// Helper predicate to check if a character is an allowed formatting character
predicate isAllowedChar(c: char)
{
    isAlphaNumeric(c) || c == '[' || c == ']' || c == '(' || c == ')' || 
    c == ',' || c == ' ' || c == '.' || c == '-' || c == '+'
}

// Helper predicate to check if all characters in a string are allowed
predicate allCharsAllowed(s: string)
{
    forall i :: 0 <= i < |s| ==> isAllowedChar(s[i])
}

// Helper predicate to check if a string starts with a given prefix
predicate startsWith(s: string, prefix: string)
{
    |s| >= |prefix| && s[0..|prefix|] == prefix
}

// Helper predicate to check if a string ends with a given suffix
predicate endsWith(s: string, suffix: string)
{
    |s| >= |suffix| && s[|s|-|suffix|..] == suffix
}

// Helper predicate to check if a string contains a specific character
predicate contains(s: string, c: char)
{
    exists i :: 0 <= i < |s| && s[i] == c
}

/**
 * Returns the string representation of an array formatted as "array([v1, v2, ..., vn])".
 * Provides a structured string representation with configurable precision and formatting options.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected for loop syntax with `for var i` and ensured integer part calculation for negative value is correct. */
function format_real(value: real, precision: nat, suppress_small: bool): string
{
    if suppress_small && -0.0000000000001 < value < 0.0000000000001 then
        "0."
    else
    (
        var s := 
            if value == 0.0 then "0." // Handle positive and negative zero consistently as "0." 
            else if value < 0.0 then "-" + format_real(-value, precision, suppress_small)
            else
            (
                var integer_part_val := value as int;
                var fractional_part_val := value - integer_part_val as real;

                var s_integer := if integer_part_val == 0 then "0" else (integer_part_val as string);

                var sb_fractional := new_string_builder();
                var temp_fractional := fractional_part_val;
                for var i := 0 to precision - 1
                    invariant 0 <= i <= precision
                    invariant 0.0 <= temp_fractional < 1.0
                {
                    temp_fractional := temp_fractional * 10.0;
                    var digit := temp_fractional as int;
                    string_builder_append_char(sb_fractional, (('0' as int) + digit) as char);
                    temp_fractional := temp_fractional - digit as real;
                }

                s_integer + "." + string_builder_to_string(sb_fractional)
            );
        
        if exists i :: 0 <= i < |s| && s[i] == '.' && forall j :: i+1 <= j < |s| ==> s[j] == '0' then
            s[0..i+1] // Trim trailing zeros after decimal point like 1.00 -> 1.
        else
            s
    )
}
// </vc-helpers>

// <vc-spec>
method array_repr(arr: seq<real>, max_line_width: nat, precision: nat, suppress_small: bool) returns (result: string)
    requires precision > 0
    requires max_line_width > 0
    ensures |result| > 0  // Non-empty result
    ensures startsWith(result, "array([")  // Basic format structure start
    ensures endsWith(result, "])")  // Basic format structure end
    ensures |arr| == 0 ==> result == "array([])"  // Empty array case
    ensures |arr| > 1 ==> contains(result, ',')  // Non-empty array case with multiple elements
    ensures |arr| == 1 ==> !contains(result, ',')  // Single element case
    ensures allCharsAllowed(result)  // Structural consistency
    ensures |result| <= max_line_width + 20  // Precision constraint
    ensures contains(result, '(') && contains(result, ')')  // Format correctness - parentheses
    ensures contains(result, '[') && contains(result, ']')  // Format correctness - brackets
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes were needed for the code body; the compilation error was resolved in the helper function. */
{
    var elements_str: seq<string> := new seq<string>(|arr|, i => format_real(arr[i], precision, suppress_small));

    var current_line_length := 0;
    var output_elements := new seq<string>(0);
    var first_element_on_line := true;
    var current_line_start_idx := 0;

    // Handle empty array case
    if |arr| == 0 {
        return "array([])";
    }

    var sb := new_string_builder();
    string_builder_append_string(sb, "array([");
    current_line_length := |("array(")|;

    var i := 0;
    while i < |elements_str|
        invariant 0 <= i <= |elements_str|
        invariant current_line_length >= 0
        invariant forall k :: 0 <= k < |string_builder_to_string(sb)| ==> isAllowedChar(string_builder_to_string(sb)[k])
    {
        var s_val := elements_str[i];
        var element_len := |s_val|;

        if i > 0 {
            // Check if adding the next element (with ', ') would exceed the max_line_width
            if current_line_length + 2 + element_len > max_line_width {
                string_builder_append_string(sb, ",\n ");
                current_line_length := 1 + element_len; // Start new line with indentation ' '
            } else {
                string_builder_append_string(sb, ", ");
                current_line_length := current_line_length + 2;
            }
        }

        string_builder_append_string(sb, s_val);
        current_line_length := current_line_length + element_len;
        i := i + 1;
    }

    string_builder_append_string(sb, "])");
    result := string_builder_to_string(sb);
}
// </vc-code>
