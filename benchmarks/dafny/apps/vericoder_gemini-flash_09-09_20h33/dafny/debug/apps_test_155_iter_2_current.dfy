predicate ValidInput(n: int, m: int, k: int) {
    n >= 2 && m >= 2 && n % 2 == 0 && k >= 0 && k < n * m
}

predicate ValidOutput(result: seq<int>, n: int, m: int) {
    |result| == 2 && result[0] >= 1 && result[0] <= n && result[1] >= 1 && result[1] <= m
}

predicate CorrectPosition(result: seq<int>, n: int, m: int, k: int) 
    requires ValidInput(n, m, k)
    requires |result| == 2
{
    if k < n then
        result[0] == k + 1 && result[1] == 1
    else
        var k_remaining := k - n;
        var r := n - k_remaining / (m - 1);
        result[0] == r &&
        (r % 2 == 1 ==> result[1] == m - k_remaining % (m - 1)) &&
        (r % 2 == 0 ==> result[1] == 2 + k_remaining % (m - 1))
}

// <vc-helpers>
predicate is_odd(a: int) {
  a % 2 == 1
}

predicate is_even(a: int) {
  a % 2 == 0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, m, k)
    ensures ValidOutput(result, n, m)
    ensures CorrectPosition(result, n, m, k)
// </vc-spec>
// <vc-code>
{
    var r: int;
    var c: int;
    if k < n {
        r := k + 1;
        c := 1;
    } else {
        var k_remaining := k - n;
        r := n - k_remaining / (m - 1);
        var offset_in_row := k_remaining % (m - 1);
        if r % 2 == 1 {
            c := m - offset_in_row;
        } else {
            c := 2 + offset_in_row;
        }
    }
    result := [r, c];
}
// </vc-code>

