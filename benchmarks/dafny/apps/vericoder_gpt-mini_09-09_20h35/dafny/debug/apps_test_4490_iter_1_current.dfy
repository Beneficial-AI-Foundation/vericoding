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
function find_newline(s: string): int
    decreases |s|
{
    if |s| == 0 then 0
    else if s[0] == '\n' then 0
    else 1 + find_newline(s[1..])
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
  var nl := find_newline(stdin_input);
  var input_line := stdin_input[..nl];
  if ValidInput(stdin_input) {
    var c := input_line[0];
    result := [DNAComplement(c)] + "\n";
  } else {
    result := "";
  }
}
// </vc-code>

