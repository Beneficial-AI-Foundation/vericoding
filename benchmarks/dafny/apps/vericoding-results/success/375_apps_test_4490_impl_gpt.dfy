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
    requires exists i :: 0 <= i < |s| && s[i] == '\n'
    ensures 0 <= find_newline(s) < |s|
    ensures s[find_newline(s)] == '\n'
    ensures forall j :: 0 <= j < find_newline(s) ==> s[j] != '\n'
    decreases |s|
{
    if s[0] == '\n' then 0 else 1 + find_newline(s[1..])
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
  if ValidInput(stdin_input) {
    var input_line :=
      if exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
      then stdin_input[..find_newline(stdin_input)]
      else stdin_input;
    assert |input_line| == 1;
    assert 0 < |input_line|;
    assert ValidDNABase(input_line[0]);
    result := [DNAComplement(input_line[0])] + "\n";
  } else {
    result := "";
  }
}
// </vc-code>

