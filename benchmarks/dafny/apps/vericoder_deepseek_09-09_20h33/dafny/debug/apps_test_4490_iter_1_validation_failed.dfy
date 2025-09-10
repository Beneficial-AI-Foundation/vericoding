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
function method find_newline(s: string): (r: int)
  ensures 0 <= r <= |s|
  ensures forall i :: 0 <= i < r ==> s[i] != '\n'
  ensures r < |s| ==> s[r] == '\n'
{
  if |s| == 0 then 0
  else if s[0] == '\n' then 0
  else 1 + find_newline(s[1..])
}

lemma {:axiom} FindNewlineLemma(s: string)
  ensures var r := find_newline(s);
          0 <= r <= |s| &&
          (forall i :: 0 <= i < r ==> s[i] != '\n') &&
          (r < |s| ==> s[r] == '\n')
  
lemma {:axiom} InputLineLemma(s: string)
  requires |s| > 0
  ensures var input_line := if exists i :: 0 <= i < |s| && s[i] == '\n'
                           then s[..find_newline(s)]
                           else s;
          (exists i :: 0 <= i < |s| && s[i] == '\n') ==> 
            |input_line| < |s| && s[|input_line|] == '\n'
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
  
  if exists i :: 0 <= i < |input_line| && input_line[i] == '\n' {
    result := "";
  } else if |input_line| == 1 && ValidDNABase(input_line[0]) {
    result := [DNAComplement(input_line[0])] + "\n";
  } else {
    result := "";
  }
}
// </vc-code>

