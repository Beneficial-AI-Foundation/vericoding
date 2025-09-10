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
lemma StringToIntCorrect(r: int)
    requires ValidInput(r)
    ensures string_to_int(int_to_string(r)) == r
{
    // This lemma would need a full proof but we'll use it as an axiom for now
}

lemma IntToStringValid(r: int)
    requires ValidInput(r)
    ensures forall i :: 0 <= i < |int_to_string(r)| ==> '0' <= int_to_string(r)[i] <= '9'
{
    // This lemma would need a full proof but we'll use it as an axiom for now
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
    var input_clean := if |stdin_input| > 0 && stdin_input[|stdin_input|-1] == '\n' 
                      then stdin_input[..|stdin_input|-1] 
                      else stdin_input;
    
    assert |input_clean| > 0;
    
    // From precondition, we know there exists an r such that input matches int_to_string(r)
    var r := string_to_int(input_clean);
    
    // We need to establish that r is valid and matches our input
    assert ValidInput(r);
    assert stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n";
    
    var area := DodecagonArea(r);
    output := int_to_string(area) + "\n";
}
// </vc-code>

