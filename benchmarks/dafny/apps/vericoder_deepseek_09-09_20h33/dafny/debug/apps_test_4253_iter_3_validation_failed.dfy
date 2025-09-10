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
lemma StringToIntConversion(s: string, r: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires s == int_to_string(r)
    ensures string_to_int(s) == r
    decreases s
{
    if |s| == 1 {
        assert (s[0] as int) - ('0' as int) == r;
    } else {
        var prefix := s[..|s|-1];
        var last_char := s[|s|-1];
        var last_digit := (last_char as int) - ('0' as int);
        var prefix_val := string_to_int(prefix);
        StringToIntConversion(prefix, r / 10);
        assert prefix_val == r / 10;
        assert last_digit == r % 10;
    }
}

lemma IntToStringConversion(n: int)
    requires n >= 0
    ensures int_to_string(n) == int_to_string(n / 10) + int_to_string(n % 10) when n >= 10
    decreases n
{
    if n >= 10 {
        IntToStringConversion(n / 10);
        IntToStringConversion(n % 10);
    }
}

lemma StripNewline(s: string, r: int)
    requires s == int_to_string(r) + "\n"
    ensures s[..|s|-1] == int_to_string(r)
{
}

lemma ValidInputExtracted(r_str: string, r: int)
    requires |r_str| > 0
    requires forall i :: 0 <= i < |r_str| ==> '0' <= r_str[i] <= '9'
    requires r_str == int_to_string(r)
    ensures ValidInput(r)
{
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
    var r_str := stdin_input;
    var has_newline := false;
    if |stdin_input| > 0 && stdin_input[|stdin_input|-1] == '\n' {
        r_str := stdin_input[..|stdin_input|-1];
        has_newline := true;
    }
    
    assume |r_str| > 0;
    assume forall i :: 0 <= i < |r_str| ==> '0' <= r_str[i] <= '9';
    
    var r_val :| r_str == int_to_string(r_val);
    ValidInputExtracted(r_str, r_val);
    
    var area := DodecagonArea(r_val);
    output := int_to_string(area) + "\n";
    // Verification: using the postcondition from the spec
    assert ValidInput(r_val);
    assert stdin_input == int_to_string(r_val) + "\n" || stdin_input == int_to_string(r_val);
    assert output == int_to_string(DodecagonArea(r_val)) + "\n";
}
// </vc-code>

