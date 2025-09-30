predicate ValidInput(r: int)
{
    1 <= r <= 100
}

function DodecagonArea(r: int): int
    requires ValidInput(r)
{
    3 * r * r
}

function int_to_string(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else int_to_string(n / 10) + int_to_string(n % 10)
}

function string_to_int(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else string_to_int(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

// <vc-helpers>
lemma int_to_string_properties(n: int)
    requires n >= 0
    ensures |int_to_string(n)| > 0
    ensures forall i :: 0 <= i < |int_to_string(n)| ==> '0' <= int_to_string(n)[i] <= '9'
{
    if n == 0 {
        // Base case
    } else if n < 10 {
        // Single digit case
    } else {
        // Recursive case
        int_to_string_properties(n / 10);
        int_to_string_properties(n % 10);
    }
}

lemma string_to_int_inverse(n: int)
    requires n >= 0
    ensures |int_to_string(n)| > 0
    ensures forall i :: 0 <= i < |int_to_string(n)| ==> '0' <= int_to_string(n)[i] <= '9'
    ensures string_to_int(int_to_string(n)) == n
    decreases n
{
    int_to_string_properties(n);  // Establish properties
    var s := int_to_string(n);
    
    if n == 0 {
        // Base case
    } else if n < 10 {
        // Single digit case
    } else {
        // Recursive case
        string_to_int_inverse(n / 10);
        string_to_int_inverse(n % 10);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires exists r: int :: ValidInput(r) && (stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n")
    ensures exists r: int :: (ValidInput(r) && 
            (stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n") &&
            output == int_to_string(DodecagonArea(r)) + "\n")
// </vc-spec>
// <vc-code>
{
    // Remove trailing newline if present
    var input_trimmed := if |stdin_input| > 0 && stdin_input[|stdin_input|-1] == '\n' 
                         then stdin_input[..|stdin_input|-1]
                         else stdin_input;
    
    // Get the witness r from the precondition
    var r :| ValidInput(r) && (stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n");
    
    // Establish that input_trimmed == int_to_string(r)
    assert input_trimmed == int_to_string(r);
    
    // Prove properties needed for string_to_int
    int_to_string_properties(r);
    assert |input_trimmed| > 0;
    assert forall i :: 0 <= i < |input_trimmed| ==> '0' <= input_trimmed[i] <= '9';
    
    // Parse the integer
    var parsed_r := string_to_int(input_trimmed);
    
    // Prove that parsed_r == r
    string_to_int_inverse(r);
    assert parsed_r == r;
    
    // Calculate the area
    var area := DodecagonArea(parsed_r);
    
    // Convert to string and add newline
    output := int_to_string(area) + "\n";
    
    // The postcondition is satisfied with witness r
    assert ValidInput(r);
    assert stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n";
    assert output == int_to_string(DodecagonArea(r)) + "\n";
}
// </vc-code>

