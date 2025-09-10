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
  ensures forall k :: 0 <= k < find_newline(s) ==> s[k] != '\n'
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant (exists idx :: 0 <= idx < |s| && s[idx] == '\n') ==> (exists idx :: i <= idx < |s| && s[idx] == '\n')
    invariant forall k :: 0 <= k < i ==> s[k] != '\n'
  {
    if s[i] == '\n' then
      return i;
    i := i + 1;
  }
  // This point should not be reached due to the precondition
  // The ghost variable and dummy return are not needed due to the precondition
  return 0; // Should be unreachable under the precondition
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
    var input_line := if exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
                      then stdin_input[..find_newline(stdin_input)]
                      else stdin_input;

    if ValidInput(stdin_input) then
        var complementary_base := DNAComplement(input_line[0]);
        result := [complementary_base] + "\n";
    else
        result := "";
}
// </vc-code>

