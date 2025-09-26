// <vc-preamble>
datatype Option<T> = None | Some(T)

predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    '\n' in stdin_input &&
    stdin_input[|stdin_input|-1] == '\n' &&
    exists r, d, n: int :: 
        0 <= d < r <= 500 && 1 <= n <= 100000 && 
        valid_pizza_input_structure(stdin_input, r, d, n)
}

predicate valid_pizza_input_structure(input: string, r: int, d: int, n: int)
{
    |input| >= 5 &&
    input[|input|-1] == '\n' &&
    0 <= d < r <= 500 &&
    1 <= n <= 100000 &&
    match parse_pizza_input(input)
        case Some((parsed_r, parsed_d, parsed_n, sausages)) => 
            parsed_r == r && parsed_d == d && parsed_n == n && |sausages| == n
        case None => false
}

function parse_pizza_input(input: string): Option<(int, int, int, seq<(int, int, int)>)>
    requires |input| > 0
    requires input[|input|-1] == '\n'
{
    Some((5, 1, 1, [(0, 0, 1)]))
}

function compute_sausages_on_crust_result(input: string): string
    requires |input| > 0
    requires '\n' in input
    requires input[|input|-1] == '\n'
    ensures |compute_sausages_on_crust_result(input)| > 0
    ensures compute_sausages_on_crust_result(input)[|compute_sausages_on_crust_result(input)|-1] == '\n'
    ensures exists count: int :: (count >= 0 && 
        compute_sausages_on_crust_result(input) == int_to_string(count) + "\n")
    ensures forall r, d, n: int, sausages: seq<(int, int, int)> ::
        (parse_pizza_input(input) == Some((r, d, n, sausages)) && 
         0 <= d < r <= 500 && 1 <= n <= 100000 && |sausages| == n) ==>
        (var count := count_sausages_on_crust(r, d, sausages);
         compute_sausages_on_crust_result(input) == int_to_string(count) + "\n" &&
         count >= 0 && count <= n)
{
    match parse_pizza_input(input)
        case Some((r, d, n, sausages)) => int_to_string(count_sausages_on_crust(r, d, sausages)) + "\n"
        case None => "0\n"
}

function count_sausages_on_crust(r: int, d: int, sausages: seq<(int, int, int)>): int
    requires 0 <= d < r <= 500
    ensures 0 <= count_sausages_on_crust(r, d, sausages) <= |sausages|
{
    if |sausages| == 0 then 0
    else 
        (if sausage_on_crust(r, d, sausages[0]) then 1 else 0) + 
        count_sausages_on_crust(r, d, sausages[1..])
}

predicate sausage_on_crust(r: int, d: int, sausage: (int, int, int))
    requires 0 <= d < r <= 500
{
    var (x, y, sausage_r) := sausage;
    var dist_sq := x * x + y * y;
    (r - d + sausage_r) * (r - d + sausage_r) <= dist_sq <= (r - sausage_r) * (r - sausage_r)
}
// </vc-preamble>

// <vc-helpers>
function int_to_string(n: int): string
    requires n >= 0
    ensures |int_to_string(n)| > 0
    ensures forall c {:trigger c in int_to_string(n)} :: c in int_to_string(n) ==> '0' <= c <= '9'
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else int_to_string(n / 10) + int_to_string(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists count: int :: (count >= 0 && result == int_to_string(count) + "\n")
    ensures forall c
// </vc-spec>
// <vc-code>
{:trigger c in result}
// </vc-code>
