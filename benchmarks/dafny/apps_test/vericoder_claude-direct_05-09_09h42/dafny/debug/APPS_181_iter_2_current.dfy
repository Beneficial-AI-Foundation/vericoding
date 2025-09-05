// ======= TASK =======
// Given a camera rotation angle, determine the minimum number of 90-degree clockwise rotations 
// needed to minimize the image's deviation from vertical orientation. Camera rotation causes 
// image to rotate in opposite direction. Goal is to minimize absolute deviation from 0 degrees.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    |input| > 0 && 
    exists trimmed :: trimmed == trim(input) && is_valid_integer_string(trimmed)
}

predicate ValidOutput(output: string)
{
    output in ["0", "1", "2", "3"]
}

predicate is_valid_integer_string(s: string)
{
    |s| > 0 &&
    (s[0] == '-' ==> |s| > 1 && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9') &&
    (s[0] != '-' ==> forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function trim(s: string): string
{
    if |s| == 0 then s
    else if s[0] == ' ' || s[0] == '\n' || s[0] == '\r' || s[0] == '\t' then
        trim(s[1..])
    else if s[|s|-1] == ' ' || s[|s|-1] == '\n' || s[|s|-1] == '\r' || s[|s|-1] == '\t' then
        trim(s[..|s|-1])
    else s
}

function string_to_int(s: string): int
    requires is_valid_integer_string(s)
{
    if |s| == 0 then 0
    else if s[0] == '-' then -parse_digits(s[1..])
    else parse_digits(s)
}

function int_to_string(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + nat_to_string(-n)
    else nat_to_string(n)
}

// <vc-helpers>
function parse_digits(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 0 then 0
    else if |s| == 1 then char_to_digit(s[0])
    else parse_digits(s[..|s|-1]) * 10 + char_to_digit(s[|s|-1])
}

function char_to_digit(c: char): int
    requires '0' <= c <= '9'
{
    c as int - '0' as int
}

function nat_to_string(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else nat_to_string(n / 10) + [('0' as int + n % 10) as char]
}

lemma int_to_string_valid(n: int)
    ensures is_valid_integer_string(int_to_string(n))
{
    if n == 0 {
        assert int_to_string(n) == "0";
        assert |"0"| == 1;
        assert '0' <= "0"[0] <= '9';
    } else if n > 0 {
        assert int_to_string(n) == nat_to_string(n);
        nat_to_string_valid(n);
    } else {
        assert int_to_string(n) == "-" + nat_to_string(-n);
        nat_to_string_valid(-n);
        assert int_to_string(n)[0] == '-';
        var digits := nat_to_string(-n);
        assert |int_to_string(n)| == 1 + |digits|;
        if |digits| > 0 {
            assert |int_to_string(n)| > 1;
            assert forall i :: 1 <= i < |int_to_string(n)| ==> int_to_string(n)[i] == digits[i-1];
        }
    }
}

lemma nat_to_string_valid(n: int)
    requires n >= 0
    ensures forall i :: 0 <= i < |nat_to_string(n)| ==> '0' <= nat_to_string(n)[i] <= '9'
{
    if n == 0 {
    } else {
        nat_to_string_valid(n / 10);
        assert ('0' as int + n % 10) as char as int == '0' as int + n % 10;
        assert 0 <= n % 10 <= 9;
        assert '0' as int <= ('0' as int + n % 10) as char as int <= '9' as int;
    }
}

lemma int_to_string_values()
    ensures int_to_string(0) == "0"
    ensures int_to_string(1) == "1"
    ensures int_to_string(2) == "2"
    ensures int_to_string(3) == "3"
{
    assert nat_to_string(1) == nat_to_string(1/10) + [('0' as int + 1%10) as char];
    assert nat_to_string(1) == nat_to_string(0) + [('0' as int + 1) as char];
    assert nat_to_string(1) == "" + [('0' as int + 1) as char];
    assert nat_to_string(1) == [('0' as int + 1) as char];
    assert ('0' as int + 1) as char == '1';
    assert nat_to_string(1) == "1";
}

lemma string_to_int_inverse(n: int)
    requires 0 <= n <= 3
    ensures string_to_int(int_to_string(n)) == n
{
    int_to_string_values();
    int_to_string_valid(n);
}

lemma modulo_properties(x: int)
    ensures 0 <= ((-x) % 360 + 360) % 360 < 360
{
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(output)
    ensures exists x :: x == string_to_int(trim(input)) &&
        exists n :: n == ((-x) % 360 + 360) % 360 &&
        exists opt, ret :: 
            opt >= 0 && opt <= 180 && ret >= 0 && ret <= 3 &&
            string_to_int(output) == ret &&
            (var pos := (n + 90 * ret) % 360;
             var deviation := if pos <= 180 then pos else 360 - pos;
             deviation == opt) &&
            (forall i :: 0 <= i <= 3 ==> 
                (var pos_i := (n + 90 * i) % 360;
                 var deviation_i := if pos_i <= 180 then pos_i else 360 - pos_i;
                 deviation_i > opt || (deviation_i == opt && i >= ret)))
// </vc-spec>
// <vc-code>
{
    var trimmed := trim(input);
    var x := string_to_int(trimmed);
    var n := ((-x) % 360 + 360) % 360;
    
    modulo_properties(x);
    
    var ret := 0;
    var pos0 := n % 360;
    var opt := if pos0 <= 180 then pos0 else 360 - pos0;
    
    var i := 1;
    while i < 4
        invariant 1 <= i <= 4
        invariant 0 <= ret <= 3
        invariant 0 <= opt <= 180
        invariant var pos := (n + 90 * ret) % 360;
                  var deviation := if pos <= 180 then pos else 360 - pos;
                  deviation == opt
        invariant forall j :: 0 <= j < i ==> 
            var pos_j := (n + 90 * j) % 360;
            var deviation_j := if pos_j <= 180 then pos_j else 360 - pos_j;
            deviation_j > opt || (deviation_j == opt && j >= ret)
    {
        var pos := (n + 90 * i) % 360;
        var deviation := if pos <= 180 then pos else 360 - pos;
        
        if deviation < opt || (deviation == opt && i < ret) {
            opt := deviation;
            ret := i;
        }
        
        i := i + 1;
    }
    
    int_to_string_values();
    string_to_int_inverse(ret);
    
    output := int_to_string(ret);
}
// </vc-code>

