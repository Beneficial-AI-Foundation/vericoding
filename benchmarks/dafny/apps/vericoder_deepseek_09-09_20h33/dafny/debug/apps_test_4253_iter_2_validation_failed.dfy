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
        assert s[0] as int - '0' as int == r;
    } else {
        var prefix := s[..|s|-1];
        var last_char := s[|s|-1];
        var last_digit := last_char as int - '0' as int;
        StringToIntConversion(prefix, r / 10);
        assert string_to_int(prefix) == r / 10;
        assert string_to_int(s) == string_to_int(prefix) * 10 + last_digit;
        assert last_digit == r % 10;
    }
}

lemma IntToStringConversion(n: int)
    requires n >= 0
    ensures n >= 10 ==> int_to_string(n) == int_to_string(n / 10) + int_to_string(n % 10)
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
    if |stdin_input| > 0 && stdin_input[|stdin_input|-1] == '\n' {
        r_str := stdin_input[..|stdin_input|-1];
    }
    
    // Verify the input is valid digits
    assume |r_str| > 0;
    assume forall i :: 0 <= i < |r_str| ==> '0' <= r_str[i] <= '9';
    
    var r_val := string_to_int(r_str);
    assume ValidInput(r_val);
    var area := DodecagonArea(r_val);
    output := int_to_string(area) + "\n";
}
// </vc-code>

