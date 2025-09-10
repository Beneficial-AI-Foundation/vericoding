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
function find_newline(s: string) : (i: int)
  requires exists i :: 0 <= i < |s| && s[i] == '\n'
  ensures 0 <= i < |s| && s[i] == '\n'
  ensures forall j :: 0 <= j < i ==> s[j] != '\n'
{
  var i : int := 0;
  while i < |s| && s[i] != '\n'
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] != '\n'
  {
    i := i + 1;
  }
  i
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
  var has_newline := exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n';
  var input_line : string;
  if has_newline {
    var idx := find_newline(stdin_input);
    input_line := stdin_input[..idx];
  } else {
    input_line := stdin_input;
  }
  if |input_line| == 1 && ValidDNABase(input_line[0]) {
    result := [DNAComplement(input_line[0])] + "\n";
  } else {
    result := "";
  }
}
// </vc-code>

