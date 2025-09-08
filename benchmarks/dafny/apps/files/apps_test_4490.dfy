Given a DNA base represented by a single letter (A, C, G, or T), find its complementary base
according to the pairing rules: A pairs with T, T pairs with A, C pairs with G, G pairs with C

predicate ValidDNABase(c: char)
{
    c in {'A', 'T', 'C', 'G'}
}

function DNAComplement(c: char): char
    requires ValidDNABase(c)
{
    match c
        case 'A' => 'T'
        case 'T' => 'A'
        case 'C' => 'G'
        case 'G' => 'C'
}

predicate ValidInput(input: string)
{
    var input_line := if exists i :: 0 <= i < |input| && input[i] == '\n'
                      then input[..find_newline(input)]
                      else input;
    |input_line| == 1 && ValidDNABase(input_line[0])
}

function find_newline(s: string): nat
    ensures find_newline(s) <= |s|
    ensures find_newline(s) < |s| ==> s[find_newline(s)] == '\n'
    ensures find_newline(s) == |s| ==> (forall i :: 0 <= i < |s| ==> s[i] != '\n')
{
    if |s| == 0 then 0
    else if s[0] == '\n' then 0
    else 1 + find_newline(s[1..])
}

method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures var input_line := if exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
                              then stdin_input[..find_newline(stdin_input)]
                              else stdin_input;
            if ValidInput(stdin_input) then
                result == [DNAComplement(input_line[0])] + "\n"
            else
                result == ""
{
    var newline_pos := find_newline(stdin_input);
    var first_line := stdin_input[..newline_pos];

    if |first_line| == 1 {
        var base := first_line[0];
        if base == 'A' {
            result := "T\n";
        } else if base == 'T' {
            result := "A\n";
        } else if base == 'C' {
            result := "G\n";
        } else if base == 'G' {
            result := "C\n";
        } else {
            result := "";
        }
    } else {
        result := "";
    }
}
