This verification task involves determining the minimum number of 90-degree clockwise rotations needed to minimize a camera image's deviation from vertical orientation. Given a camera rotation angle, the algorithm must find the optimal number of rotations (0-3) that brings the image closest to 0 degrees deviation.

The implementation needs to handle camera rotation causing image rotation in the opposite direction, normalize angles to 0-360 degrees, and find the rotation count that minimizes absolute deviation from vertical.

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

// ======= HELPERS =======
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
{
    var trimmed := trim(input);
    var x := string_to_int(trimmed);

    var n := ((-x) % 360 + 360) % 360;

    var ret := 0;
    var pos0 := n % 360;
    var opt := if pos0 <= 180 then pos0 else 360 - pos0;

    for i := 0 to 4
        invariant 0 <= ret <= 3
        invariant opt <= 180
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

        if deviation < opt || (deviation == opt && i < ret)
        {
            opt := deviation;
            ret := i;
        }
    }

    assert ret >= 0 && ret <= 3;
    assert int_to_string(0) == "0";
    assert int_to_string(1) == "1";
    assert int_to_string(2) == "2";
    assert int_to_string(3) == "3";

    assert x == string_to_int(trim(input));
    assert n == ((-x) % 360 + 360) % 360;
    assert opt >= 0 && opt <= 180 && ret >= 0 && ret <= 3;
    var pos := (n + 90 * ret) % 360;
    var deviation := if pos <= 180 then pos else 360 - pos;
    assert deviation == opt;
    assert forall i :: 0 <= i <= 3 ==> 
        var pos_i := (n + 90 * i) % 360;
        var deviation_i := if pos_i <= 180 then pos_i else 360 - pos_i;
        deviation_i > opt || (deviation_i == opt && i >= ret);

    output := int_to_string(ret);
    assert string_to_int(output) == ret;

    return output;
}
