Calculate the area of a regular dodecagon inscribed in a circle of radius r.
The area formula is 3r². Input is an integer r (1 ≤ r ≤ 100).
Output is the integer area.

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

lemma lemma_int_to_string_nonempty(n: int)
    requires n >= 0
    ensures |int_to_string(n)| > 0
{
    if n == 0 {
    } else if n < 10 {
    } else {
        lemma_int_to_string_nonempty(n / 10);
        lemma_int_to_string_nonempty(n % 10);
    }
}

lemma lemma_int_to_string_digits(n: int)
    requires n >= 0
    ensures forall i :: 0 <= i < |int_to_string(n)| ==> '0' <= int_to_string(n)[i] <= '9'
{
    if n == 0 {
    } else if n < 10 {
    } else {
        lemma_int_to_string_digits(n / 10);
        lemma_int_to_string_digits(n % 10);
    }
}

lemma lemma_string_int_inverse(n: int)
    requires n >= 0
    ensures |int_to_string(n)| > 0
    ensures forall i :: 0 <= i < |int_to_string(n)| ==> '0' <= int_to_string(n)[i] <= '9'
    ensures string_to_int(int_to_string(n)) == n
{
    lemma_int_to_string_nonempty(n);
    lemma_int_to_string_digits(n);

    if n == 0 {
    } else if n < 10 {
        var s := [('0' as int + n) as char];
        assert |s| == 1;
        assert string_to_int(s) == (s[0] as int) - ('0' as int);
        assert s[0] == ('0' as int + n) as char;
        assert (s[0] as int) == ('0' as int + n);
        assert string_to_int(s) == n;
    } else {
        var s := int_to_string(n);
        lemma_string_int_inverse(n / 10);
        lemma_string_int_inverse(n % 10);
    }
}

method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires exists r: int :: ValidInput(r) && (stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n")
    ensures exists r: int :: (ValidInput(r) && 
            (stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n") &&
            output == int_to_string(DodecagonArea(r)) + "\n")
{
    var r_str := if stdin_input[|stdin_input|-1] == '\n' then stdin_input[..|stdin_input|-1] else stdin_input;

    var r_val :| ValidInput(r_val) && (stdin_input == int_to_string(r_val) || stdin_input == int_to_string(r_val) + "\n");

    assert r_str == int_to_string(r_val);

    lemma_int_to_string_digits(r_val);
    assert forall i :: 0 <= i < |r_str| ==> '0' <= r_str[i] <= '9';

    var r := string_to_int(r_str);

    lemma_string_int_inverse(r_val);
    assert r == r_val;
    assert ValidInput(r);
    assert stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n";

    var area := DodecagonArea(r);
    output := int_to_string(area) + "\n";

    assert ValidInput(r) && 
           (stdin_input == int_to_string(r) || stdin_input == int_to_string(r) + "\n") &&
           output == int_to_string(DodecagonArea(r)) + "\n";
}
