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
function find_newline(s: string): nat
    requires exists i :: 0 <= i < |s| && s[i] == '\n'
    ensures 0 <= find_newline(s) < |s|
    ensures s[find_newline(s)] == '\n'
    ensures forall i :: 0 <= i < find_newline(s) ==> s[i] != '\n'
{
    find_newline_helper(s, 0)
}

function find_newline_helper(s: string, start: nat): nat
    requires start <= |s|
    requires exists i :: start <= i < |s| && s[i] == '\n'
    ensures start <= find_newline_helper(s, start) < |s|
    ensures s[find_newline_helper(s, start)] == '\n'
    ensures forall i :: start <= i < find_newline_helper(s, start) ==> s[i] != '\n'
    decreases |s| - start
{
    if start < |s| && s[start] == '\n' then
        start
    else
        find_newline_helper(s, start + 1)
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
    var input_line: string;
    
    // Check if there's a newline in the input
    var has_newline := false;
    var newline_pos := 0;
    var i := 0;
    while i < |stdin_input|
        invariant 0 <= i <= |stdin_input|
        invariant !has_newline ==> forall j :: 0 <= j < i ==> stdin_input[j] != '\n'
        invariant has_newline ==> 0 <= newline_pos < |stdin_input| && stdin_input[newline_pos] == '\n'
        invariant has_newline ==> forall j :: 0 <= j < newline_pos ==> stdin_input[j] != '\n'
    {
        if stdin_input[i] == '\n' {
            has_newline := true;
            newline_pos := i;
            break;
        }
        i := i + 1;
    }
    
    // Extract input_line based on whether newline was found
    if has_newline {
        assert exists j :: 0 <= j < |stdin_input| && stdin_input[j] == '\n';
        assert newline_pos == find_newline(stdin_input);
        input_line := stdin_input[..newline_pos];
    } else {
        input_line := stdin_input;
    }
    
    // Check validity and compute result
    if |input_line| == 1 && ValidDNABase(input_line[0]) {
        var complement := DNAComplement(input_line[0]);
        result := [complement] + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

