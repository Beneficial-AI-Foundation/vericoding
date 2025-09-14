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

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, m, k)
    ensures ValidOutput(result, n, m)
    ensures CorrectPosition(result, n, m, k)
// </vc-spec>
// <vc-code>
{
  if k < n {
    // The first n steps (k=0 to k=n-1) go down the first column.
    result := [k + 1, 1];
  } else {
    // After the first column, the path continues in a snake-like pattern
    // for the remaining m-1 columns.
    var k_remaining := k - n;
    
    // Each row in the snake part has m-1 cells.
    // 'r_block' is the number of full snake-rows traversed.
    var r_block := k_remaining / (m - 1);
    // 'c_step' is the step within the current snake-row.
    var c_step := k_remaining % (m - 1);

    // The snake traversal starts from row 'n' and moves upwards.
    var r := n - r_block;
    var c: int;

    // The direction of traversal depends on the row's parity.
    // n is even, so row n is even. Traversal is left-to-right (2..m).
    // Row n-1 is odd. Traversal is right-to-left (m..2).
    // An even row 'r' moves left-to-right. An odd row 'r' moves right-to-left.
    if r % 2 == 0 { // even
      c := 2 + c_step;
    } else { // odd
      c := m - c_step;
    }
    result := [r, c];
  }
}
// </vc-code>

