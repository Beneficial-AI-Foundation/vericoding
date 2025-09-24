// <vc-preamble>
predicate ValidInput(N: int, M: int) {
    1 <= N <= 100000 && 1 <= M <= 1000000000
}

function sequences_with_product_count_mod(N: int, M: int): int
    requires N > 0 && M > 0
    ensures 0 <= sequences_with_product_count_mod(N, M) < 1000000007
{
    0  // Placeholder implementation
}

function string_of_int(n: int): string
    requires n >= 0
    ensures |string_of_int(n)| > 0
    ensures forall i :: 0 <= i < |string_of_int(n)| ==> '0' <= string_of_int(n)[i] <= '9'
{
    "0"  // Placeholder implementation
}

predicate ValidOutput(result: string, count: int) {
    |result| > 0 &&
    result[|result|-1] == '\n' &&
    (forall i :: 0 <= i < |result|-1 ==> '0' <= result[i] <= '9') &&
    0 <= count < 1000000007 &&
    result == string_of_int(count) + "\n"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists N, M :: 
        ValidInput(N, M) && 
        stdin_input == string_of_int(N) + " " + string_of_int(M) + "\n"
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures forall i :: 0 <= i < |result|-1 ==> '0' <= result[i] <= '9'
    ensures exists N, M :: 
        ValidInput(N, M) && 
        stdin_input == string_of_int(N) + " " + string_of_int(M) + "\n" &&
        (var count := sequences_with_product_count_mod(N, M);
         result == string_of_int(count) + "\n")
// </vc-spec>
// <vc-code>
{
    var N, M :| ValidInput(N, M) && 
                stdin_input == string_of_int(N) + " " + string_of_int(M) + "\n";

    var count := sequences_with_product_count_mod(N, M);

    result := string_of_int(count) + "\n";
}
// </vc-code>
