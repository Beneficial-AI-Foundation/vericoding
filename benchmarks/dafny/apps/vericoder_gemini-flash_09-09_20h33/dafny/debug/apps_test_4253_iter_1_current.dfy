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
function method IsSuffix(s: string, suffix: string): bool
  reads s, suffix
  ensures IsSuffix(s, suffix) <==> (|s| >= |suffix| && s[|s|-|suffix|..] == suffix)
{
  |s| >= |suffix| && s[|s|-|suffix|..] == suffix
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
    var r_str: string := stdin_input;
    if IsSuffix(stdin_input, "\n") {
        r_str := stdin_input[..|stdin_input|-1];
    }
    
    var r: int := string_to_int(r_str);
    var area: int := DodecagonArea(r);
    output := int_to_string(area) + "\n";
}
// </vc-code>

