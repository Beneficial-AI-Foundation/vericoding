predicate is_binary_string(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

predicate is_valid_integer(s: string)
{
    |s| > 0 && (s[0] != '0' || |s| == 1) && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function count_char(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function abs_diff_count(s: string): int
    requires is_binary_string(s)
{
    var count0 := count_char(s, '0');
    var count1 := count_char(s, '1');
    if count1 >= count0 then count1 - count0 else count0 - count1
}

function int_to_string(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [char_of_digit(n)]
    else int_to_string(n / 10) + [char_of_digit(n % 10)]
}

function char_of_digit(d: int): char
    requires 0 <= d <= 9
{
    match d
        case 0 => '0'
        case 1 => '1' 
        case 2 => '2'
        case 3 => '3'
        case 4 => '4'
        case 5 => '5'
        case 6 => '6'
        case 7 => '7'
        case 8 => '8'
        case 9 => '9'
}

function string_to_int(s: string): int
    requires is_valid_integer(s)
{
    if |s| == 0 then 0
    else if |s| == 1 then (s[0] as int) - ('0' as int)
    else string_to_int(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

// <vc-helpers>
lemma int_to_string_is_valid(n: int)
    requires n >= 0
    ensures is_valid_integer(int_to_string(n))
{
    if n == 0 {
        assert int_to_string(0) == "0";
        assert is_valid_integer("0");
    } else if n < 10 {
        var s := int_to_string(n);
        assert s == [char_of_digit(n)];
        assert |s| == 1;
        assert s[0] == char_of_digit(n);
        assert '0' <= s[0] <= '9';
        assert is_valid_integer(s);
    } else {
        var s := int_to_string(n);
        int_to_string_is_valid(n / 10);
        var prefix := int_to_string(n / 10);
        assert is_valid_integer(prefix);
        assert s == prefix + [char_of_digit(n % 10)];
        assert |s| > 1;
        assert s[0] == prefix[0];
        assert prefix[0] != '0' || |prefix| == 1;
        if |prefix| == 1 && prefix[0] == '0' {
            assert prefix == int_to_string(n / 10);
            assert prefix == "0";
            assert int_to_string(n / 10) == "0";
            assert n / 10 < 1;
            assert n / 10 >= 0;
            assert n / 10 == 0;
            assert n < 10;
            assert false;
        }
        assert s[0] != '0';
        forall i | 0 <= i < |s|
            ensures '0' <= s[i] <= '9'
        {
            if i < |prefix| {
                assert s[i] == prefix[i];
                assert '0' <= prefix[i] <= '9';
            } else {
                assert i == |s| - 1;
                assert s[i] == char_of_digit(n % 10);
                assert '0' <= s[i] <= '9';
            }
        }
        assert is_valid_integer(s);
    }
}

lemma FirstNewlineIsValid(stdin_input: string, newline_pos: int)
    requires |stdin_input| > 0
    requires 0 <= newline_pos < |stdin_input|
    requires stdin_input[newline_pos] == '\n'
    requires forall j :: 0 <= j < newline_pos ==> stdin_input[j] != '\n'
    requires exists np :: 0 <= np < |stdin_input| && stdin_input[np] == '\n' &&
             np + 1 < |stdin_input| &&
             (exists be :: np + 1 <= be <= |stdin_input| &&
             (be == |stdin_input| || stdin_input[be] == '\n') &&
             is_valid_integer(stdin_input[0..np]) &&
             is_binary_string(stdin_input[np + 1..be]))
    ensures newline_pos + 1 < |stdin_input|
    ensures is_valid_integer(stdin_input[0..newline_pos])
    ensures exists be :: newline_pos + 1 <= be <= |stdin_input| &&
            (be == |stdin_input| || stdin_input[be] == '\n') &&
            is_binary_string(stdin_input[newline_pos + 1..be])
{
    // The precondition tells us there exists some valid newline position np
    // We found the first newline at newline_pos
    // Since we found the first one, newline_pos <= np
    var np :| 0 <= np < |stdin_input| && stdin_input[np] == '\n' &&
              np + 1 < |stdin_input| &&
              (exists be :: np + 1 <= be <= |stdin_input| &&
              (be == |stdin_input| || stdin_input[be] == '\n') &&
              is_valid_integer(stdin_input[0..np]) &&
              is_binary_string(stdin_input[np + 1..be]));
    
    if newline_pos < np {
        // We found a newline before np, but this contradicts that np satisfies the precondition
        assert stdin_input[newline_pos] == '\n';
        assert false; // Contradiction - np cannot satisfy the precondition if there's an earlier newline
    }
    
    // Therefore newline_pos == np
    assert newline_pos == np;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
    requires exists newline_pos :: 0 <= newline_pos < |stdin_input| && stdin_input[newline_pos] == '\n' &&
             newline_pos + 1 < |stdin_input| &&
             exists binary_end :: newline_pos + 1 <= binary_end <= |stdin_input| &&
             (binary_end == |stdin_input| || stdin_input[binary_end] == '\n') &&
             is_valid_integer(stdin_input[0..newline_pos]) &&
             is_binary_string(stdin_input[newline_pos + 1..binary_end])
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists newline_pos :: 0 <= newline_pos < |stdin_input| && stdin_input[newline_pos] == '\n' &&
            newline_pos + 1 < |stdin_input| &&
            exists binary_end :: newline_pos + 1 <= binary_end <= |stdin_input| &&
            (binary_end == |stdin_input| || stdin_input[binary_end] == '\n') &&
            is_binary_string(stdin_input[newline_pos + 1..binary_end]) &&
            result == int_to_string(abs_diff_count(stdin_input[newline_pos + 1..binary_end])) + "\n"
// </vc-spec>
// <vc-code>
{
    // Find the first newline
    var newline_pos := 0;
    while newline_pos < |stdin_input| && stdin_input[newline_pos] != '\n'
        invariant 0 <= newline_pos <= |stdin_input|
        invariant forall j :: 0 <= j < newline_pos ==> stdin_input[j] != '\n'
    {
        newline_pos := newline_pos + 1;
    }
    
    // From precondition, we know there exists a newline
    assert newline_pos < |stdin_input|;
    assert stdin_input[newline_pos] == '\n';
    
    // Use the lemma to establish that this first newline is the valid one
    FirstNewlineIsValid(stdin_input, newline_pos);
    
    // Now we know the properties hold for this newline_pos
    assert is_valid_integer(stdin_input[0..newline_pos]);
    assert newline_pos + 1 < |stdin_input|;
    
    // Find the end of the binary string (next newline or end of input)
    var binary_end := newline_pos + 1;
    while binary_end < |stdin_input| && stdin_input[binary_end] != '\n'
        invariant newline_pos + 1 <= binary_end <= |stdin_input|
        invariant forall j :: newline_pos + 1 <= j < binary_end ==> stdin_input[j] != '\n'
    {
        binary_end := binary_end + 1;
    }
    
    // Extract the binary string
    var binary_string := stdin_input[newline_pos + 1..binary_end];
    
    // From the lemma, we know there exists a valid binary_end
    // We found the first position that's either end of input or newline
    // This must be a valid binary_end
    var be :| newline_pos + 1 <= be <= |stdin_input| &&
              (be == |stdin_input| || stdin_input[be] == '\n') &&
              is_binary_string(stdin_input[newline_pos + 1..be]);
    
    // Our binary_end is the first such position, so it must equal be
    if binary_end < be {
        // binary_end is either end of input or a newline
        if binary_end == |stdin_input| || stdin_input[binary_end] == '\n' {
            // But be also satisfies this, contradicting minimality
            assert false;
        }
    } else if binary_end > be {
        // be is either end of input or contains a newline
        if be < |stdin_input| {
            assert stdin_input[be] == '\n';
            // But we would have stopped at be
            assert false;
        } else {
            assert be == |stdin_input|;
            assert binary_end > |stdin_input|;
            assert false;
        }
    }
    assert binary_end == be;
    assert is_binary_string(binary_string);
    
    // Calculate the absolute difference
    var diff := abs_diff_count(binary_string);
    assert diff >= 0;
    
    // Convert to string
    var diff_str := int_to_string(diff);
    int_to_string_is_valid(diff);
    
    // Construct result
    result := diff_str + "\n";
    
    // Verify postconditions
    assert |result| > 0;
    assert result[|result|-1] == '\n';
    assert result == int_to_string(abs_diff_count(stdin_input[newline_pos + 1..binary_end])) + "\n";
}
// </vc-code>

