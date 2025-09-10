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
    ensures 0 <= find_newline(s) <= |s|
{
    if |s| == 0 then 0
    else if s[0] == '\n' then 0
    else 1 + find_newline(s[1..])
}

lemma find_newline_bounds(s: string)
    ensures 0 <= find_newline(s) <= |s|
    decreases |s|
{
    if |s| == 0 {
    } else {
      if s[0] == '\n' {
      } else {
        find_newline_bounds(s[1..]);
      }
    }
}

lemma ValidInputProperties(s: string)
    ensures ValidInput(s) ==>
        (if exists i :: 0 <= i < |s| && s[i] == '\n'
         then |s[..find_newline(s)]| == 1 && ValidDNABase(s[..find_newline(s)][0])
         else |s| == 1 && ValidDNABase(s[0]))
{
    if !ValidInput(s) {
    } else {
      var input_line := if exists i :: 0 <= i < |s| && s[i] == '\n' then s[..find_newline(s)] else s;
      assert |input_line| == 1 && ValidDNABase(input_line[0]);
      if exists i :: 0 <= i < |s| && s[i] == '\n' {
        assert |s[..find_newline(s)]| == 1;
        assert ValidDNABase(s[..find_newline(s)][0]);
      } else {
        assert |s| == 1;
        assert ValidDNABase(s[0]);
      }
    }
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
  if ValidInput(stdin_input) {
    ValidInputProperties(stdin_input);
    assert |input_line| == 1;
    var c := input_line[0];
    result := [DNAComplement(c)] + "\n";
  } else {
    result := "";
  }
}
// </vc-code>

