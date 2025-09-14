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

// <vc-helpers>
function find_newline(s: string): (res: nat)
    ensures 0 <= res <= |s|
    ensures (exists i :: 0 <= i < |s| && s[i] == '\n') ==>
            (0 <= res < |s| && s[res] == '\n' && (forall j :: 0 <= j < res ==> s[j] != '\n'))
    ensures (forall i :: 0 <= i < |s| ==> s[i] != '\n') ==>
            res == |s|
    decreases |s|
{
    if |s| == 0 then
        |s|
    else if s[0] == '\n' then
        0
    else
        var rest_idx := find_newline(s[1..]);
        if rest_idx == |s[1..]| then
            |s|
        else
            1 + rest_idx
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures var input_line := if exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
                              then stdin_input[..find_newline(stdin_input)]
                              else stdin_input;
            if ValidInput(stdin_input) then
                result == [DNAComplement(input_line[0])] + "\n"
            else
                result == ""
// </vc-spec>
// <vc-code>
{
    var newline_idx := find_newline(stdin_input);
    var input_line := stdin_input[..newline_idx];

    if |input_line| == 1 && ValidDNABase(input_line[0]) {
        result := [DNAComplement(input_line[0])] + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

